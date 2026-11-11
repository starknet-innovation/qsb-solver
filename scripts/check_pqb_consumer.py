"""Check a pinned qsb-app checkout against this worker, using public CPU fixtures only.

python3 scripts/check_pqb_consumer.py APP_CHECKOUT APP_COMMIT NEW_OUTPUT_DIR

Install the consumer's locked dependencies first (npm ci --ignore-scripts). This script
uses its actual TypeScript implementation and focused tests; it launches no service,
hardware or transaction and enrolls no release. Both checkouts must be clean.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TS = r'''
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
const app=process.argv[2], worker=process.argv[3];
const {pqbWorkRange}=await import(pathToFileURL(app+'/server/pqb-search.ts').href);
const {parsePacket,problemFromPacket,problemTxt,HitChecker,parseStrictDer}=await import(pathToFileURL(app+'/src/pqb-core/grind.ts').href);
const {hex}=await import(pathToFileURL(app+'/src/pqb-core/primitives.ts').href);
const ranges=[];
for(const [stage,n] of [['round1',70],['round2',174]])
 for(let attempt=0;attempt<n;attempt++) ranges.push({stage:stage==='round1'?'round0':'round1',attempt,range:pqbWorkRange(stage,attempt)});
for(const attempt of [0,1,2,76695844,153391687,153391688,...Array.from({length:100},(_,i)=>(i*15485863)%153391689)])
 ranges.push({stage:'pinning',attempt,range:pqbWorkRange('pinning',attempt)});
const expected=JSON.parse(readFileSync(worker+'/research/pqb-ranked/measure/expected.json','utf8'));
const base=worker+'/research/pqb-ranked/tests/fixtures/';
const packet=parsePacket(readFileSync(base+'pin.packet.json','utf8'));
const filters=expected.cases.filter(c=>c.label.startsWith('pin-der-filter-emits')).map(c=>{
 const prob=problemFromPacket(packet,c.gateBits),checker=new HitChecker(packet,prob,c.gateBits);
 if(problemTxt(prob)!==readFileSync(base+'pin.txt','utf8').replace('gate_bits 12\n','gate_bits '+c.gateBits+'\n')) throw Error('Problem differs');
 return {label:c.label,gateBits:c.gateBits,hits:c.hits.map(line=>{const hit=checker.check(line);return {line,digest:hex(hit.digest),strictDer:parseStrictDer(hit.digest)!==null}}),canonical:checker.canonical,fullSolutions:checker.full};
});
console.log(JSON.stringify({ranges,filters}));
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True).strip()


def check(app, expected_commit, out):
    app, out = app.resolve(), out.resolve()
    if out.is_relative_to(ROOT) or out.is_relative_to(app):
        raise ValueError('Keep evidence outside both source checkouts')
    if git(app, 'rev-parse', 'HEAD') != expected_commit or len(expected_commit) != 40:
        raise ValueError('Consumer commit mismatch; supply the full pinned commit')
    if git(app, 'status', '--porcelain') or git(ROOT, 'status', '--porcelain'):
        raise ValueError('Both source checkouts must be clean')
    if (app/'contracts/pqb-ranked-v2.json').read_bytes() != (ROOT/'contracts/pqb-ranked-v2.json').read_bytes():
        raise ValueError('Consumer contract bytes differ')
    out.mkdir(parents=True, exist_ok=False)
    (out/'result.json').write_text('{"status":"started"}\n')
    tsx, vitest = app/'node_modules/.bin/tsx', app/'node_modules/.bin/vitest'
    receipt = {'format':'qsb-pqb-consumer-check-v1', 'status':'failed',
               'workerCommit':git(ROOT, 'rev-parse', 'HEAD'), 'consumerCommit':expected_commit,
               'contractFileSha256':sha(ROOT/'contracts/pqb-ranked-v2.json'),
               'consumerLockSha256':sha(app/'package-lock.json'),
               'limits':['CPU fixture/range checks only; reduced gate for filter fixtures',
                         'Consumer tests mock providers and positive coordinator verdicts',
                         'No native full solve, Batch transport, consensus/spend or enrollment']}
    try:
        harness = out/'consumer-check.mts'
        harness.write_text(TS)
        done = subprocess.run([str(tsx), str(harness), str(app), str(ROOT)], cwd=app,
                              capture_output=True, text=True, timeout=120)
        (out/'implementation.stdout').write_text(done.stdout)
        (out/'implementation.stderr').write_text(done.stderr)
        done.check_returncode()
        data = json.loads(done.stdout)
        sys.path.insert(0, str(ROOT/'worker/pqb'))
        from pqb_ranges import work_range
        from pqb_handler import parse_problem
        for row in data['ranges']:
            if work_range(row['stage'], row['attempt']) != row['range']:
                raise ValueError('Range mismatch: '+str(row))
        fixture = json.loads((app/'tests/fixtures/pqb-reference.json').read_text())
        problems = []
        for stage, case in zip(('pinning','round0','round1'), fixture['stages'], strict=True):
            raw = case['problem'].encode()
            parse_problem(raw, stage)
            problems.append({'stage':stage,'sha256':hashlib.sha256(raw).hexdigest()})
        tests = ['tests/pqb.test.ts','tests/pqb-protocol.test.ts','tests/pqb-sdk.test.ts']
        done = subprocess.run([str(vitest),'run',*tests], cwd=app,
                              env={**os.environ,'QSB_NETWORK':'mainnet'}, capture_output=True,
                              text=True, timeout=180)
        (out/'tests.stdout').write_text(done.stdout)
        (out/'tests.stderr').write_text(done.stderr)
        done.check_returncode()
        receipt.update(status='passed',rangeComparisons=len(data['ranges']),
                       publicProblems=problems,filterCandidates=data['filters'],consumerTests=tests,
                       numberParsing='Consumer documents JSON 1.0 normalizing to wire integer 1; raw Python float token remains invalid')
    except Exception as error:
        receipt['error']=str(error)
    receipt['files']={p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file() and p.name!='result.json'}
    (out/'result.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'status':receipt['status'],'rangeComparisons':receipt.get('rangeComparisons')}))
    return 0 if receipt['status']=='passed' else 1


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('consumer',type=Path)
    parser.add_argument('commit')
    parser.add_argument('output',type=Path)
    args=parser.parse_args()
    sys.exit(check(args.consumer,args.commit,args.output))
