"""Check simulated installed-wrapper envelopes against the pinned real CPU consumer."""
import argparse,json,os
from pathlib import Path
import subprocess

TS=r'''
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
const [app,input]=process.argv.slice(2);
const {proposal,replay}=JSON.parse(readFileSync(input,'utf8'));
const provenance=await import(pathToFileURL(app+'/src/lib/provenance.ts').href);
const {checkedOutput,assertSolverRuntime}=await import(pathToFileURL(app+'/server/search-protocol.ts').href);
const {parsePacket,problemFromPacket,problemTxt,HitChecker}=await import(pathToFileURL(app+'/src/pqb-core/grind.ts').href);
assert.equal(replay.simulatedGrinder,true);assert.equal(replay.freshNativeExecution,false);
const solver=provenance.externalSolverDescriptorSchema.parse(proposal.solver);
assertSolverRuntime(solver);provenance.assertPaidSolverContract(solver);
assert.equal(provenance.solverRegistry([solver]).get(solver.id),provenance.canonical(solver));
assert.throws(()=>provenance.solverRegistry([solver,solver]));
assert.throws(()=>provenance.solverRegistry([{...solver,searchContract:'0'.repeat(64)}]));
const stages=[];
for(const row of replay.rows){
 const raw=row.response,stage=raw.stage==='round0'?'round1':raw.stage==='round1'?'round2':'pinning';
 const job:any={stage,manifestHash:raw.manifestHash};
 const {output}=checkedOutput(raw,solver,job,raw.attempt);
 assert.equal(output.status,'completed');
 assert.throws(()=>checkedOutput({...raw,kernelCommit:'0'.repeat(40)},solver,job,raw.attempt));
 assert.throws(()=>checkedOutput({...raw,searchVersion:'ranked-v2'},solver,job,raw.attempt));
 const packet=parsePacket(row.packet),problem=problemFromPacket(packet,24);
 assert.equal(problemTxt(problem),row.problem);
 const checker=new HitChecker(packet,problem,24);
 for(const hit of output.candidates)checker.check(hit);
 stages.push({stage:row.stage,candidates:output.candidates.length,consumerChecks:checker.stats()});
}
console.log(JSON.stringify({status:'passed',stages,simulatedGrinder:true,freshNativeExecution:false,
 scope:'Actual installed-wrapper metadata compatibility and independent CPU checks of retained hit fixtures',
 computeSubmitted:false,enrolled:false,creditGranted:false}));
'''


def check(app,commit,replay,proposal,out):
    def git(*args):return subprocess.check_output(['git','-C',str(app),*args],text=True).strip()
    if git('rev-parse','HEAD')!=commit or git('status','--porcelain'):raise ValueError('Consumer must be clean and pinned')
    out.mkdir(exist_ok=False);(out/'check.mts').write_text(TS)
    (out/'input.json').write_text(json.dumps(dict(replay=json.loads(replay.read_bytes()),proposal=json.loads(proposal.read_bytes()))))
    result=subprocess.run([str(app/'node_modules/.bin/tsx'),str(out/'check.mts'),str(app),str(out/'input.json')],
        cwd=app,env={**os.environ,'QSB_NETWORK':'mainnet'},capture_output=True,text=True,timeout=120)
    (out/'stdout').write_text(result.stdout);(out/'stderr').write_text(result.stderr);result.check_returncode()
    receipt=json.loads(result.stdout);receipt.update(format='qsb-pqb-wrapper-consumer-replay-v1',consumerCommit=commit)
    (out/'result.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('app',type=Path);p.add_argument('commit')
    p.add_argument('replay',type=Path);p.add_argument('proposal',type=Path);p.add_argument('out',type=Path)
    a=p.parse_args();check(a.app.resolve(),a.commit,a.replay,a.proposal,a.out.resolve())
