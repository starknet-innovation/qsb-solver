"""Prepare full-transaction CPU vectors and a diagnostic pinning trace.

This module allocates no hardware and launches no solver. The proposed diagnostic
prints full recovered-key hashes before the existing predicate. A future native
run must bind source, compiler, diagnostic and exact release binary identities.
"""
import argparse
import base64
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys

VERSION = 'qsb-config-a-cmsverify-v1'
TRACE = re.compile(r'TRACE_PIN sequence=([0-9]+) locktime=([0-9]+) recid=([01]) hash=([0-9a-f]{64})')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def instrument(source):
    anchor = '        int vv;'
    if source.count(anchor) != 1:
        raise ValueError('Pinning trace anchor changed')
    trace = ('        printf("TRACE_PIN sequence=%u locktime=%u recid=%d hash='
             '%08x%08x%08x%08x%08x%08x%08x%08x\\n",seq_value,lt,ri,'
             'hs[0],hs[1],hs[2],hs[3],hs[4],hs[5],hs[6],hs[7]);\n')
    return source.replace(anchor, trace+anchor)


def verify_trace(log, expected):
    actual = {}
    for line in log.splitlines():
        if not line.startswith('TRACE_PIN'):
            continue
        match = TRACE.fullmatch(line)
        if match is None:
            raise ValueError('Malformed pinning trace')
        seq, lt, recid, digest = match.groups()
        key = ':'.join((seq, lt, recid))
        if key in actual:
            raise ValueError('Duplicate pinning lane')
        actual[key] = digest
    if actual != expected:
        raise ValueError('Missing, extra, or mismatching pinning hash')
    return len(actual)


def prepare(app, fixture, output):
    if output.exists():
        raise ValueError('New output required')
    provenance = json.loads((fixture/'provenance.json').read_text())
    if provenance['scriptVersion'] != VERSION:
        raise ValueError('Wrong script version')
    for name, digest in provenance['files'].items():
        if sha(fixture/name) != digest:
            raise ValueError('Fixture changed: '+name)
    for name, digest in provenance['sourceFiles'].items():
        if sha(app/name) != digest:
            raise ValueError('CPU reference changed: '+name)
    sys.path.insert(0, str(app/'public/qsb'))
    from bitcoin_tx import Transaction, TxIn, TxOut, find_and_delete, classify_qsb_script
    from secp256k1 import ecdsa_recover, compress_pubkey
    state = json.loads((fixture/'public-state.json').read_text())
    if classify_qsb_script(state) != VERSION:
        raise ValueError('Wrong exact script')
    txdata = json.loads((fixture/'gpu_pinning_params.json').read_text())['spending_tx']
    script = find_and_delete(bytes.fromhex(state['full_script_hex']), bytes.fromhex(state['pin_sig']))
    cases = []
    for sequence in (0x80000000, 0xffffffff):
        for locktime in (500000000, 500000063, 500000127, 500000255, 1744599996):
            expected, sighashes = {}, {}
            for lt in range(locktime, locktime+4):
                tx = Transaction(version=txdata['version'], locktime=lt)
                for label in ('extra_input', 'qsb_input'):
                    item = txdata[label]
                    tx.add_input(TxIn(bytes.fromhex(item['txid']), item['vout'], b'',
                        sequence if label == 'qsb_input' else item['sequence']))
                out = txdata['output']
                tx.add_output(TxOut(out['value'], bytes.fromhex(out['script_pubkey'])))
                z = tx.sighash(txdata['qsb_input_index'], script, txdata['sighash_type'])
                sighashes[f'{sequence}:{lt}'] = z.to_bytes(32,'big').hex()
                for recid in (0,1):
                    point = ecdsa_recover(state['pin_r'], state['pin_s'], z, recid)
                    if point is None:
                        raise ValueError('Exceptional vector requires a separate diagnostic')
                    expected[f'{sequence}:{lt}:{recid}'] = hashlib.sha256(compress_pubkey(point)).hexdigest()
            cases.append(dict(sequence=sequence,locktime=locktime,sequenceCount=1,locktimeCount=4,
                              expected=expected,sighashes=sighashes))
    plan = dict(status='PREPARED_NOT_EXECUTED',scriptVersion=VERSION,provenanceSha256=sha(fixture/'provenance.json'),
                sourceFiles=provenance['sourceFiles'],parameterSha256=sha(fixture/'pinning.bin'),
                parameterBase64=base64.b64encode((fixture/'pinning.bin').read_bytes()).decode(),
                scriptCodeSha256=hashlib.sha256(script).hexdigest(),cases=cases,
                expectedHashes=sum(len(c['expected']) for c in cases),
                limits='Diagnostic recovered-key hashes only; not real-hit, exact-binary coverage, fresh withdrawal or miner evidence')
    with output.open('x') as stream:
        json.dump(plan,stream,indent=2); stream.write('\n')
    return plan


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode',required=True)
    p = sub.add_parser('prepare')
    for name in ('app','fixture','output'):
        p.add_argument('--'+name,type=Path,required=True)
    p = sub.add_parser('instrument')
    p.add_argument('--source',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    if args.mode == 'prepare':
        prepare(args.app.resolve(),args.fixture.resolve(),args.output.resolve())
    else:
        original = args.source.read_text()
        changed = instrument(original)
        # Do not overwrite either a release source or earlier diagnostic evidence.
        with args.output.open('x') as stream:
            stream.write(changed)
        print(''.join(difflib.unified_diff(original.splitlines(True),changed.splitlines(True),
                                         fromfile='repaired/pinning.cu',tofile='diagnostic/pinning-trace.cu')),end='')


if __name__ == '__main__':
    main()
