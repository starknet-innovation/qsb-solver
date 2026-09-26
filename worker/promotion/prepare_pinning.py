"""Combined-candidate-only fail-closed host repairs; historical source stays intact."""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def repair(text):
    main = text.index('int main(')
    prefix, body = text[:main], text[main:]
    # Standalone CUDA statements only. Existing assigned/checked calls stay intact.
    # SLOTPIPE=0 is enforced: other geometries have different completion semantics.
    sites = []
    masked = re.sub(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"',
                    lambda m: ''.join('\n' if c == '\n' else ' ' for c in m[0]), body, flags=re.S)
    masked = re.sub(r'^[ \t]*#[^\n]*', lambda m: ' ' * len(m[0]), masked, flags=re.M)
    edits = []
    names = r'cuda(?:SetDevice|GetDeviceProperties|Malloc|Memcpy|MemcpyToSymbol|Memset|DeviceSynchronize|DeviceSetLimit|DeviceGetAttribute|GetDeviceCount)'
    for match in re.finditer(names + r'\(', masked):
        before = masked[:match.start()].rstrip()
        if not before or before[-1] not in ';{}':
            continue  # assigned, conditional, or already checked expression
        depth, end = 1, match.end()
        while depth:
            depth += (masked[end] == '(') - (masked[end] == ')')
            end += 1
        if not masked[end:].lstrip().startswith(';'):
            continue
        call = body[match.start():end]
        sites.append(call)
        edits.append((match.start(),end,'QSB_PIN_CUDA_REQUIRE('+call+')'))
    for start,end,replacement in reversed(edits):
        body = body[:start]+replacement+body[end:]
    cap = 'int nh = (h_hit > 64) ? 64 : h_hit;'
    if body.count(cap) != 2:
        raise ValueError('bounded pinning readback branches changed')
    body = body.replace(cap, 'if (h_hit > 64) { fprintf(stderr,"QSB_RANGE_INCOMPLETE: hit capacity exceeded\\n"); return 2; }\n                int nh = (int)h_hit;')
    start = body.index('                FILE *f = fopen(fname, "a");', body.index('#else\n    for (uint64_t seq64'))
    end = body.index('                found = 1;', start)
    old = body[start:end]
    if 'fclose(f);' not in old or old.count('fprintf(f,') != 1:
        raise ValueError('pinning publisher changed')
    body = body[:start] + '''                if (!qsb_publish_pinning_hits(fname, seq, batch_lt, hits, nh)) {
                    fprintf(stderr,"QSB_RANGE_INCOMPLETE: cannot publish pinning hits\\n");
                    return 2;
                }
''' + body[end:]
    guard = '''
#if QSB_SLOTPIPE != 0
#error "Combined repaired pinning supports only QSB_SLOTPIPE=0"
#endif
#include "pinning_output.h"
#define QSB_PIN_CUDA_REQUIRE(call) do { cudaError_t qsb_error=(call); if(qsb_error!=cudaSuccess){fprintf(stderr,"QSB_RANGE_INCOMPLETE: %s: %s\\n",#call,cudaGetErrorString(qsb_error));return 2;} } while(0)
'''
    return prefix + guard + body, sites


def main():
    subprocess.run([sys.executable, str(ROOT/'worker/prepare_kernels.py')], check=True)
    source = ROOT/'worker/build/pinning'
    output = Path(sys.argv[1]).resolve()
    shutil.copytree(source, output)
    path = output/'pinning.cu'
    original = path.read_text(); patched, sites = repair(original)
    path.write_text(patched)
    shutil.copyfile(ROOT/'worker/promotion/pinning_output.h',output/'pinning_output.h')
    receipt = dict(guardedCalls=sites, adaptedInputSha256=hashlib.sha256(original.encode()).hexdigest(),
                   repairedSourceSha256=hashlib.sha256(patched.encode()).hexdigest(),
                   scope='Combined-only host failure handling; CUDA predicates and arithmetic unchanged')
    (output/'host-repair.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__ == '__main__':
    main()
