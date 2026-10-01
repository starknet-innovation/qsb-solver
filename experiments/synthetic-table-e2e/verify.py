"""Revalidate collected synthetic receipts and all child outputs offline."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import run

def validate(files,binary,image,command_exit):
    run.require(type(command_exit) is int and command_exit==0 and files['exit-code.txt'].strip()=='0','host failed')
    run.require(re.fullmatch('[0-9a-f]{64}',binary) and files['binary.sha256'].split()==[binary,'table-gate'],'binary mismatch')
    run.require(re.fullmatch(r'ghcr.io/starknet-innovation/qsb-solver@sha256:[0-9a-f]{64}',image) and files['runtime.txt'].strip()==image,'runtime mismatch')
    gpu=files['gpu.txt'].strip().splitlines();run.require(len(gpu)==1 and gpu[0].split(',')[0].strip()=='NVIDIA A10G','wrong GPU inventory')
    fields=[x.strip() for x in gpu[0].split(',')];run.require(len(fields)==3 and all(fields) and fields[1].startswith('GPU-'),'incomplete GPU identity')
    result=run.strict_json(files['result.json'])
    run.require(result['binarySha256']==binary and result['noSolverSearch'] is True and result['solverThroughputMeasured'] is False,'result identity/scope mismatch')
    run.require(result['measurementScope']==run.SCOPE,'wrong measurement scope')
    summary=run.summarize(result);run.require(result['summary']==summary,'summary mismatch')
    for check in result['sanitizers']:
        stem=check['tool']+'-'+check['arm'];log=files[stem+'.log']
        run.require(run.strict_json(files[stem+'.json'])==check['report'],'sanitizer report mismatch')
        run.require(hashlib.sha256(log.encode()).hexdigest()==check['logSha256'],'sanitizer log hash mismatch')
        wanted='========= RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)' if check['tool']=='racecheck' else '========= ERROR SUMMARY: 0 errors'
        run.require('COMPUTE-SANITIZER' in log and log.count(run.COMPLETE)==1 and [x.strip() for x in log.splitlines() if 'SUMMARY:' in x]==[wanted],'unclean sanitizer')
    for sample in result['samples']:
        stem=f"sample-{sample['repetitions']}-{sample['pair']}-{sample['arm']}"
        run.require(run.strict_json(files[stem+'.json'])==sample['report'],'sample report mismatch')
        run.require(files[stem+'.log'].count(run.COMPLETE)==1,'sample completion missing')
    return dict(status='passed',binarySha256=binary,runtime=image,noSolverSearch=True,solverThroughputMeasured=False,measurementScope=result['measurementScope'],summary=summary,evidenceSha256={k:hashlib.sha256(v.encode()).hexdigest() for k,v in files.items()})

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('envelope',type=Path);p.add_argument('output',type=Path);p.add_argument('--binary',required=True);p.add_argument('--image',required=True);p.add_argument('--command-exit',type=int,required=True);a=p.parse_args()
    result=validate(run.strict_json(a.envelope.read_text()),a.binary,a.image,a.command_exit)
    with a.output.open('x') as f:json.dump(result,f,indent=2,allow_nan=False)
if __name__=='__main__':main()
