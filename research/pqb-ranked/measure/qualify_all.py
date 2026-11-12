"""Three separately bounded final-image units in one freshly armed 60-minute session."""
import json
from pathlib import Path
import sys
import time
from qualify_image import run as single
from run_full_unit import write_json, sha256, STAGES


def run(gate,result,deadline,*,runner=single,now=time.time):
    gate,result=Path(gate),Path(result)
    result.mkdir()  # one-shot marker; never resume or repeat this output directory
    out=dict(format='qsb-pqb-final-image-all-v1',status='incomplete',deadline=int(deadline),stages=[])
    write_json(result/'result.json',out)
    for stage in STAGES:
        if int(deadline)-now()<1100:
            out.update(status='failed',error='Insufficient fixed-deadline margin; next unit not started')
            break
        row=runner(gate,result/stage,stage)
        out['stages'].append(dict(stage=stage,status=row['status'],resultPath=stage+'/result.json',
                                 resultSha256=sha256(result/stage/'result.json')))
        write_json(result/'result.json',out)
        if row['status']!='passed':
            out.update(status='failed',error='A unit failed; subsequent work not started')
            break
    else:
        out['status']='passed'
    write_json(result/'result.json',out)
    return out


if __name__=='__main__':
    result=run(*sys.argv[1:])
    print(json.dumps(result))
    raise SystemExit(0 if result['status']=='passed' else 1)
