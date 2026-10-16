"""Run public-only corrected stages serially; no provisioning or signing.

Host credentials are limited to pre-created checkpoint upload URLs. This script
never places them inside a container. External fixed shutdown remains mandatory.
"""
import argparse
import json
from pathlib import Path
import subprocess
from campaign_supervisor import supervise

IMAGE='ghcr.io/starknet-innovation/qsb-solver@sha256:d22c9b5842eca2eca1d8f27f45d7760f213fdaa4e01511de1eda77541ef51e47'
PIN='cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62'
SUBSET='673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15'

def command(bundle,output,acks,stage,deadline,solution=None):
    name='qsb-fresh-'+stage
    args=['docker','run','--rm','--network=none','--read-only','--cap-drop=ALL',
          '--security-opt=no-new-privileges','--gpus=all','--tmpfs','/tmp:rw,size=2g',
          '--name='+name,'-v',str(bundle)+':/bundle:ro','-v',str(output)+':/output:rw',
          '-v',str(acks)+':/acks:ro']
    if solution:
        args+=['-v',str(solution)+':/solution.json:ro']
    binary='pinning' if stage=='pinning' else 'subset'
    args+=['--entrypoint','python3',IMAGE,'/bundle/worker/promotion/validation/fresh_'+binary+'_search.py',
           '--public','/bundle/fresh-export-pinning.json','--reference','/bundle/reference',
           '--reference-hashes','/bundle/reference-hashes.json','--binary','/opt/qsb/'+binary,
           '--binary-sha256',PIN if stage=='pinning' else SUBSET,'--output','/output',
           '--intent-ack-dir','/acks','--deadline',str(deadline),'--range-timeout','840']
    if solution:args+=['--solution','/solution.json','--stage',stage]
    return name,args

def run(bundle,root,url_dir,deadline):
    paths=[bundle.resolve(),root.resolve(),url_dir.resolve()]
    if any(a==b or a in b.parents or b in a.parents for i,a in enumerate(paths) for b in paths[i+1:]):
        raise ValueError('Bundle, output and upload capability directories must be disjoint')
    # A pipeline is one-shot. Only explicit reconciled operator work may resume it.
    root.mkdir(parents=True,exist_ok=False)
    solution=None
    for stage in ('pinning','round1','round2'):
        output=root/stage;acks=root/(stage+'-acks')
        output.mkdir();acks.mkdir()
        name,args=command(bundle,output,acks,stage,deadline,solution)
        result=supervise(output,acks,args,deadline,(url_dir/(stage+'.url')).read_text().strip(),name)
        (root/(stage+'-status.json')).write_text(json.dumps(result,indent=2)+'\n')
        if result['status']!='verified-hit':return {'status':'partial-stop','stage':stage,'result':result}
        solution=output/'solution.json'
        if not solution.is_file():raise ValueError('Verified solution artifact missing')
    return {'status':'all-puzzles-cpu-verified','solution':json.loads(solution.read_text()),
            'withdrawal':'NOT_RUN; offline Core verification remains local'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for field in ('bundle','output','upload-url-dir'):
        parser.add_argument('--'+field,type=Path,required=True)
    parser.add_argument('--deadline',type=int,required=True)
    args=parser.parse_args()
    try:
        print(json.dumps(run(args.bundle.resolve(),args.output.resolve(),args.upload_url_dir.resolve(),args.deadline)))
    finally:
        # Root host runner exits on partial progress, failure or success. Retaining
        # an idle GPU until the watchdog deadline is not part of the campaign.
        subprocess.run(['/sbin/shutdown','-h','now'],check=False,timeout=10)

if __name__=='__main__':main()
