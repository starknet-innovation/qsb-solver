"""Build host-fault diagnostic separately from the normal repaired executable."""
import hashlib
import json
from pathlib import Path
import subprocess


def instrument(source):
    start = source.index('#define QSB_PIN_CUDA_REQUIRE(call)')
    end = source.index('\n', start)
    macro = r'''static unsigned qsb_audit_call = 0;
#define QSB_PIN_CUDA_REQUIRE(call) do { unsigned ordinal=++qsb_audit_call; fprintf(stderr,"QSB_AUDIT_CALL %u %s\n",ordinal,#call); const char *fault=getenv("QSB_AUDIT_FAIL"); cudaError_t qsb_error=(fault && strtoul(fault,0,10)==ordinal)?cudaErrorUnknown:(call); if(qsb_error!=cudaSuccess){fprintf(stderr,"QSB_RANGE_INCOMPLETE: %s: %s\n",#call,cudaGetErrorString(qsb_error));return 2;} } while(0)'''
    result = source[:start]+macro+source[end:]
    marker = 'if (h_hit > 64) { fprintf(stderr,"QSB_RANGE_INCOMPLETE: hit capacity exceeded'
    if result.count(marker) != 2:
        raise ValueError('capacity guards changed')
    result = result.replace(marker, 'if (getenv("QSB_AUDIT_OVERFLOW")) h_hit=65;\n                '+marker)
    return result


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = Path('/opt/repaired-pinning/pinning.cu')
    output = Path('/opt/qsb-pinning-audit'); output.mkdir()
    diagnostic = source.with_name('pinning-audit.cu')
    diagnostic.write_text(instrument(source.read_text()))
    flags = ['-O3','-arch=sm_89','-DQSB_SLOTPIPE=0']
    subprocess.run(['nvcc',*flags,'-o',str(output/'pinning-audit'),str(diagnostic),'-lcrypto','-lm'],check=True)
    import shutil
    shutil.copyfile('/pinning',output/'pinning')
    receipt = dict(flags=flags, sourceSha256=sha(source), diagnosticSourceSha256=sha(diagnostic),
        files={p.name:sha(p) for p in output.iterdir() if p.is_file()},
        compiler=subprocess.check_output(['nvcc','--version'],text=True),
        scope='Host-call error and counter injection only; derivative is never a release solver',status='UNEXECUTED')
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__ == '__main__':
    main()
