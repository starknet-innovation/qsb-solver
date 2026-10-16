"""Build diagnostic full-hash pinning trace beside the unchanged executable."""
import difflib
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
from corrected_pinning_trace import instrument

def main():
    source = Path('/opt/repaired-pinning/pinning.cu')
    output = Path('/opt/qsb-pinning-trace'); output.mkdir()
    original = source.read_text()
    diagnostic = source.with_name('pinning-trace.cu')
    diagnostic.write_text(instrument(original))
    architecture = source.with_name('cuda-architecture').read_text().strip()
    if architecture not in ('86', '89'):
        raise ValueError('Unexpected architecture')
    flags = ['-O3', '-arch=sm_'+architecture, '-DQSB_SLOTPIPE=0']
    subprocess.run(['nvcc', *flags, '-o', str(output/'pinning-trace'), str(diagnostic), '-lcrypto', '-lm'], check=True)
    shutil.copyfile('/pinning', output/'pinning')
    (output/'trace.diff').write_text(''.join(difflib.unified_diff(original.splitlines(True), diagnostic.read_text().splitlines(True), fromfile='repaired/pinning.cu', tofile='diagnostic/pinning-trace.cu')))
    sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
    receipt = dict(flags=flags, architecture='sm_'+architecture, sourceSha256=sha(source), diagnosticSourceSha256=sha(diagnostic), files={p.name:sha(p) for p in output.iterdir() if p.is_file()}, compiler=subprocess.check_output(['nvcc','--version'],text=True), scope='Full hash diagnostic derivative; not final executable coverage attestation', status='UNEXECUTED')
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')

if __name__ == '__main__':
    main()
