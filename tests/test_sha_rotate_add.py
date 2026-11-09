"""Offline checks for the isolated SHA rotate-add experiment. No compiler, no GPU."""
import hashlib, json, pathlib, random, re, shutil, struct, subprocess, sys, tempfile, unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXP = ROOT / 'experiments/sha-rotate-add'
sys.path.insert(0, str(EXP))
import compare_sass  # noqa: E402

M = 0xffffffff
K = [0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
     0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
     0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
     0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2]
IV = [0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19]


def ror(x, n): return ((x >> n) | (x << (32 - n))) & M
def ch(e, f, g): return g ^ (e & (f ^ g))
def maj(a, b, c): return (a & b) | (c & (a | b))


def reference_round(a, b, c, d, e, f, g, h, kw):
    t1 = (h + (ror(e,6) ^ ror(e,11) ^ ror(e,25)) + ch(e,f,g) + kw) & M
    t2 = ((ror(a,2) ^ ror(a,13) ^ ror(a,22)) + maj(a,b,c)) & M
    return (d + t1) & M, (t1 + t2) & M


def patched_source():
    lock = json.loads((EXP / 'experiment-lock.json').read_text())
    with tempfile.TemporaryDirectory() as tmp:
        work = pathlib.Path(tmp); (work / 'subset').mkdir()
        shutil.copyfile(ROOT / 'research/optimized-subset/subset/GPUHash.h', work / 'subset/GPUHash.h')
        subprocess.run(['patch', '--batch', '-p1', '-i', str(EXP / 'sha-rotate-add.patch')], cwd=work, check=True, capture_output=True)
        data = (work / 'subset/GPUHash.h').read_bytes()
    return lock, data


def asm_blocks(text, macro):
    """Every definition of `macro`: (PTX statements, operand names in %N order)."""
    found = []
    for match in re.finditer(r'#define ' + re.escape(macro) + r'\(.*?\n(?=#|/\*)', text, re.S):
        body = match.group(0)
        start = body.index('asm(')
        literals, _, constraints = body[start:].partition(': "')
        code = ''.join(re.findall(r'"((?:[^"\\]|\\.)*)"', literals)).replace('\\n', '\n').replace('\\t', ' ')
        statements = [s.strip() for s in code.replace('{', '').replace('}', '').split(';') if s.strip() and not s.strip().startswith('.reg')]
        names = re.findall(r'"[+=]?[rn]"\((\w+)\)', ': "' + constraints)
        found.append((statements, names))
    return found


def run_ptx(statements, names, values):
    regs = {}
    def get(tok):
        tok = tok.strip()
        return values[names[int(tok[1:])]] if tok.startswith('%') else (regs[tok] if tok in regs else int(tok, 0))
    def put(tok, v):
        tok = tok.strip()
        if tok.startswith('%'): values[names[int(tok[1:])]] = v & M
        else: regs[tok] = v & M
    for statement in statements:
        op, _, rest = statement.partition(' '); args = rest.split(',')
        if op == 'add.u32': put(args[0], get(args[1]) + get(args[2]))
        elif op == 'sub.u32': put(args[0], get(args[1]) - get(args[2]))
        elif op == 'shf.r.wrap.b32':
            n = get(args[3]) & 31; put(args[0], (get(args[1]) >> n) | (get(args[2]) << (32 - n)))
        else: raise AssertionError('Unmodelled PTX: ' + statement)
    return values


class Identity(unittest.TestCase):
    def test_lock_binds_patch_baseline_and_upstream_result(self):
        lock, patched = patched_source()
        production = json.loads((ROOT / 'worker/optimized/source-lock.json').read_text())
        self.assertEqual(hashlib.sha256((EXP / 'sha-rotate-add.patch').read_bytes()).hexdigest(), lock['patchSha256'])
        self.assertEqual(production['files']['subset/GPUHash.h'], lock['baselineGpuHashSha256'])
        self.assertEqual(hashlib.sha256((ROOT / 'research/optimized-subset/subset/GPUHash.h').read_bytes()).hexdigest(), lock['baselineGpuHashSha256'])
        self.assertEqual(hashlib.sha256(patched).hexdigest(), lock['patchedGpuHashSha256'])
        self.assertEqual(lock['status'], 'HOLD')

    def test_patch_touches_only_gpuhash(self):
        files = re.findall(r'^\+\+\+ b/(\S+)', (EXP / 'sha-rotate-add.patch').read_text(), re.M)
        self.assertEqual(files, ['subset/GPUHash.h'])


class RoundModel(unittest.TestCase):
    """Runs the patch's own PTX text through a three-opcode interpreter. The C parts are transcribed by hand."""
    @classmethod
    def setUpClass(cls):
        text = patched_source()[1].decode()
        cls.rla_asm = asm_blocks(text, 'QSB_LEA_RLA'); cls.rlm_d_asm = asm_blocks(text, 'QSB_LEA_RLM_D')

    def rla(self, form, a, b, c, d, e, f, g, h, kw):
        statements, names = self.rla_asm[form]
        v = run_ptx(statements, names, {'d': d, 'h': h, 'qx_': (h + kw) & M, 'qch_': ch(e,f,g), 'qmj_': maj(a,b,c),
                                        'qy_': e ^ ror(e,5) ^ ror(e,19), 'qz_': a ^ ror(a,11) ^ ror(a,20)})
        return v['d'], v['h']

    def rlm(self, form, a, b, c, d, e, f, g, h, kw):
        statements, names = self.rlm_d_asm[form]
        qy, qz, qmj = e ^ ror(e,5) ^ ror(e,19), a ^ ror(a,11) ^ ror(a,20), maj(a,b,c)
        qt = (h + kw + ch(e,f,g) + qmj + ror(qy,6)) & M
        v = run_ptx(statements, names, {'d': d, 'qt_': qt, 'qmj_': qmj})
        return v['d'], (qt + ror(qz,2)) & M

    def test_both_definitions_of_each_form_were_found(self):
        self.assertEqual(len(self.rla_asm), 2); self.assertEqual(len(self.rlm_d_asm), 2)
        self.assertEqual(self.rla_asm[0][1], ['d', 'h', 'qx_', 'qch_', 'qmj_', 'qy_', 'qz_'])

    def test_every_round_form_equals_the_reference_round(self):
        rnd = random.Random(8); edge = [0, 1, M, 0x80000000, 0x7fffffff]
        cases = [[rnd.choice(edge) for _ in range(9)] for _ in range(2000)] + [[rnd.getrandbits(32) for _ in range(9)] for _ in range(20000)]
        for case in cases:
            want = reference_round(*case)
            for form in (0, 1):
                self.assertEqual(self.rla(form, *case), want); self.assertEqual(self.rlm(form, *case), want)

    def compress(self, round_function, block):
        w = list(struct.unpack('>16I', block)); s = list(IV)
        for i in range(16, 64):
            s0 = ror(w[i-15],7) ^ ror(w[i-15],18) ^ (w[i-15] >> 3); s1 = ror(w[i-2],17) ^ ror(w[i-2],19) ^ (w[i-2] >> 10)
            w.append((w[i-16] + s0 + w[i-7] + s1) & M)
        a, b, c, d, e, f, g, h = s
        for i in range(64):
            d, h = round_function(a, b, c, d, e, f, g, h, (K[i] + w[i]) & M)
            a, b, c, d, e, f, g, h = h, a, b, c, d, e, f, g
        return struct.pack('>8I', *[(x + y) & M for x, y in zip(s, (a, b, c, d, e, f, g, h))])

    def test_full_compression_matches_hashlib(self):
        rnd = random.Random(9)
        for length in list(range(0, 56)) * 4:
            message = bytes(rnd.getrandbits(8) for _ in range(length))
            block = message + b'\x80' + bytes(55 - length) + struct.pack('>Q', 8 * length)
            want = hashlib.sha256(message).digest()
            for form in (0, 1):
                self.assertEqual(self.compress(lambda *x: self.rla(form, *x), block), want)
                self.assertEqual(self.compress(lambda *x: self.rlm(form, *x), block), want)


SASS_A = """
Fatbin elf code:
		Function : _Z13kernel_digestPKh
	.headerflags    @"EF_CUDA_SM86"
        /*0000*/                   MOV R1, c[0x0][0x28] ;          /* 0x00000a0000017a02 */
        /*0010*/                   SHF.R.W.U32 R2, R3, 0x6, R3 ;   /* 0x0000000603027819 */
        /*0020*/                   IADD3 R4, R2, R5, R6 ;          /* 0x0000000502047210 */
        /*0030*/              @!P0 EXIT ;                          /* 0x000000000000094d */
		Function : helper
        /*0000*/                   RET.REL.NODEC R20 `(helper) ;   /* 0x0000000014007950 */
"""
SASS_B = SASS_A.replace('SHF.R.W.U32 R2, R3, 0x6, R3 ;   /* 0x0000000603027819 */\n        /*0020*/                   IADD3 R4, R2, R5, R6 ; ',
                        'LEA.HI R4, R3, R5, R3, 0x1a ;  /* 0x0000000503047211 */\n        /*0020*/                   NOP ;')


class Sass(unittest.TestCase):
    def test_summary_counts_instructions_per_function(self):
        s = compare_sass.summarise(SASS_A)
        self.assertEqual(s['instructions'], 5)
        self.assertEqual(s['functions']['_Z13kernel_digestPKh']['opcodes'], {'EXIT': 1, 'IADD3': 1, 'MOV': 1, 'SHF.R.W.U32': 1})
        self.assertEqual(s['functions']['helper']['instructions'], 1)

    def test_comparison_reports_only_differences(self):
        a, b = compare_sass.summarise(SASS_A), compare_sass.summarise(SASS_B)
        d = compare_sass.compare(a, b)
        self.assertFalse(d['identicalSass']); self.assertEqual(d['instructions'], 0); self.assertEqual(d['leaInstructions'], 1)
        self.assertEqual(d['opcodes'], {'IADD3': -1, 'LEA.HI': 1, 'NOP': 1, 'SHF.R.W.U32': -1})
        self.assertEqual(list(d['functions']), ['_Z13kernel_digestPKh'])
        self.assertTrue(compare_sass.compare(a, a)['identicalSass'])

    def test_empty_listing_is_rejected(self):
        with self.assertRaises(ValueError): compare_sass.summarise('no code here')


if __name__ == '__main__':
    unittest.main()
