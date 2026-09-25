"""Bounded exact-image A10G public-fixture gate; not a fresh withdrawal proof."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time
from benchmark import execute, hit_fields

COMMIT = '43c77084648aa0f4cbcb1589abfcc792c9cc0d9d'
PIN = 'cd70b2c2a7bcf129a9259c494413d5b2995368361e294e7bd284380d58df7a62'
SUB = '673ad624ae1ceba184ed7219abf81641507412134c7bdc4224e3fc9defc5df15'

def validate_binding(binding):
    if binding.get('solverCommit') != COMMIT or binding.get('architecture') != 'sm_86':
        raise ValueError('Wrong source or architecture')
    if binding.get('files',{}).get('pinning') != PIN or binding['files'].get('subset') != SUB:
        raise ValueError('Wrong native binaries')

def main():
    sys.path.insert(0,'/opt/qsb')
    import handler
    binding=handler.release_binding();validate_binding(binding)
    gpu=subprocess.check_output(['nvidia-smi','--query-gpu=name,uuid,driver_version','--format=csv,noheader'],text=True).strip()
    if len(gpu.splitlines()) != 1 or 'A10G' not in gpu:
        raise ValueError('Exactly one A10G required')
    output=Path(sys.argv[1])
    # A retained file is a one-shot intent, including failed/uncertain runs.
    with output.open('x') as stream:json.dump(dict(status='running',binding=binding,gpu=gpu),stream)
    fixtures=json.loads(Path(__file__).with_name('fixtures.json').read_text())
    result=dict(status='running',binding=binding,gpu=gpu,replays=[],ranges=[],freshWithdrawal=False)
    deadline=time.monotonic()+600
    for fixture in fixtures['replay']:
        row=execute(Path('/opt/qsb/subset'),fixture,1,fixture['rank'],deadline)
        if hit_fields(row['hit']) != hit_fields(fixture['expected']):raise ValueError('Known replay mismatch')
        result['replays'].append(dict(name=fixture['name'],**row))
    for fixture in fixtures['benchmark']:
        for start,count in [(0,1),(63,257),(65535,65537),(0,2**26)]:
            row=execute(Path('/opt/qsb/subset'),fixture,count,start,deadline)
            if row['hit']:raise ValueError('Unexpected candidate requires independent CPU verification')
            result['ranges'].append(dict(name=fixture['name'],**row))
    result['status']='completed'
    temporary=output.with_suffix('.tmp');temporary.write_text(json.dumps(result,indent=2)+'\n');temporary.replace(output)
    print(json.dumps(dict(status='completed',replays=len(result['replays']),ranges=len(result['ranges']),resultSha256=hashlib.sha256(output.read_bytes()).hexdigest())),flush=True)

if __name__=='__main__':main()
