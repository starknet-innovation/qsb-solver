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
    # Counter overrides must precede the positive-hit branch. The synthetic
    # record tests host publication only and never represents a real GPU hit.
    anchors = [
        ('h_hit = hit_report[0];', 'hit_report[1]=0;'),
        ('QSB_PIN_CUDA_REQUIRE(cudaMemcpy(&h_hit, d_hit_cnt, 4, cudaMemcpyDeviceToHost));',
         'if(cudaMemset(d_hit_idx,0,4)!=cudaSuccess) return 2;'),
    ]
    for anchor, initialize in anchors:
        if result.count(anchor) != 1:
            raise ValueError('counter readback anchor changed')
        result = result.replace(anchor, anchor + '\n' +
            'if(getenv("QSB_AUDIT_HIT")) { '+initialize+' h_hit=1; }\n' +
            'if(getenv("QSB_AUDIT_OVERFLOW")) h_hit=65;')
    return result


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    source = Path('/opt/repaired-pinning/pinning.cu')
    output = Path('/opt/qsb-pinning-audit'); output.mkdir()
    diagnostic = source.with_name('pinning-audit.cu')
    diagnostic.write_text(instrument(source.read_text()))
    architecture = source.with_name('cuda-architecture').read_text().strip()
    if architecture not in ('86','89'): raise ValueError('unexpected repaired pinning architecture')
    flags = ['-O3','-arch=sm_'+architecture,'-DQSB_SLOTPIPE=0']
    subprocess.run(['nvcc',*flags,'-o',str(output/'pinning-audit'),str(diagnostic),'-lcrypto','-lm'],check=True)
    import shutil
    shutil.copyfile('/pinning',output/'pinning')
    receipt = dict(flags=flags, architecture='sm_'+architecture, sourceSha256=sha(source), diagnosticSourceSha256=sha(diagnostic),
        files={p.name:sha(p) for p in output.iterdir() if p.is_file()},
        compiler=subprocess.check_output(['nvcc','--version'],text=True),
        scope='Host-call error and counter injection only; derivative is never a release solver',status='UNEXECUTED')
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__ == '__main__':
    main()
