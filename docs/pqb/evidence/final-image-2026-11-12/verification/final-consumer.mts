
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
const [app,input]=process.argv.slice(2);
const {proposal,rows}=JSON.parse(readFileSync(input,'utf8'));
const mod=await import(pathToFileURL(app+'/src/lib/provenance.ts').href);
const {checkedOutput,assertSolverRuntime}=await import(pathToFileURL(app+'/server/search-protocol.ts').href);
const {parsePacket,problemFromPacket,problemTxt,HitChecker}=await import(pathToFileURL(app+'/src/pqb-core/grind.ts').href);
const solver=mod.externalSolverDescriptorSchema.parse(proposal.solver);
assertSolverRuntime(solver);mod.assertPaidSolverContract(solver);
assert.equal(mod.solverRegistry([solver]).get(solver.id),mod.canonical(solver));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse(proposal));
assert.throws(()=>mod.solverRegistry([solver,solver]));
assert.throws(()=>mod.solverRegistry([{...solver,searchContract:'0'.repeat(64)}]));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse({...solver,generatorCommit:'0'.repeat(40)}));
assert.throws(()=>mod.solverRelease(solver.id),/UnsupportedSolverRelease/);
const results=[];
for(const row of rows){
 const raw=row.response,stage=raw.stage==='round0'?'round1':raw.stage==='round1'?'round2':'pinning';
 const job:any={stage,manifestHash:raw.manifestHash};
 const {output,range}=checkedOutput(raw,solver,job,raw.attempt);
 assert.equal(output.status,'completed');
 assert.throws(()=>checkedOutput({...raw,kernelCommit:'0'.repeat(40)},solver,job,raw.attempt));
 assert.throws(()=>checkedOutput({...raw,searchVersion:'ranked-v2'},solver,job,raw.attempt));
 assert.throws(()=>checkedOutput({...raw,workRange:{...raw.workRange,start:'1'}},solver,job,raw.attempt));
 const packet=parsePacket(row.packet),prob=problemFromPacket(packet,24);
 assert.equal(problemTxt(prob),row.problem);
 const checker=new HitChecker(packet,prob,24);
 for(const hit of output.candidates)checker.check(hit);
 const mean=raw.trials/2**24;
 assert.ok(Math.abs(raw.gateHits-mean)<=6*Math.sqrt(mean)+6);
 results.push({stage:row.stage,attempt:raw.attempt,candidates:output.candidates.length,
   consumerChecks:checker.stats(),workerSeconds:row.workerSeconds,jobSeconds:row.jobSeconds});
}
console.log(JSON.stringify({status:'passed',schema:3,stages:results,enrolled:false,
  publicationVerified:false,scope:'Fresh exact-image native envelopes and CPU cryptographic checks',
  limits:['No new complete solve, served Step Functions, wallet, consensus, miner or broadcast test',
  'Six-sigma gate sanity checked separately; served consumer only enforces accounting bounds']}));
