
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
const [app,input]=process.argv.slice(2);
const {proposal,rows}=JSON.parse(readFileSync(input,'utf8'));
const mod=await import(pathToFileURL(app+'/src/lib/provenance.ts').href);
const {checkedOutput,assertSolverRuntime}=await import(pathToFileURL(app+'/server/search-protocol.ts').href);
const solver=mod.externalSolverDescriptorSchema.parse(proposal.solver);
assertSolverRuntime(solver);mod.assertPaidSolverContract(solver);
assert.equal(mod.solverRegistry([solver]).get(solver.id),mod.canonical(solver));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse(proposal));
assert.throws(()=>mod.solverRegistry([solver,solver]));
assert.throws(()=>mod.solverRegistry([{...solver,searchContract:'0'.repeat(64)}]));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse({...solver,image:proposal.binding.privateValidationImage}));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse({...solver,generatorCommit:'0'.repeat(40)}));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse({...solver,searchVersion:'ranked-v2'}));
assert.throws(()=>mod.solverRelease(solver.id),/UnsupportedSolverRelease/);
const stages:any={pinning:0,round1:0,round2:0};let hits=0,minZ=Infinity,maxZ=-Infinity;
for(const {name,envelope} of rows){
 const raw=envelope.output;
 const stage=raw.stage==='round0'?'round1':raw.stage==='round1'?'round2':'pinning';
 const job:any={stage,manifestHash:raw.manifestHash};
 const {output,range}=checkedOutput(raw,solver,job,raw.attempt);
 assert.equal(output.status,'completed');
 assert.throws(()=>checkedOutput({...raw,kernelCommit:'0'.repeat(40)},solver,job,raw.attempt));
 assert.throws(()=>checkedOutput({...raw,workRange:{...raw.workRange,start:'1'}},solver,job,raw.attempt));
 const width=stage==='pinning'?72:stage==='round1'?192:64;
 const mean=range.count*width/2**24,z=(raw.gateHits-mean)/Math.sqrt(mean);
 assert.ok(Number.isSafeInteger(raw.gateHits)&&Math.abs(raw.gateHits-mean)<=6*Math.sqrt(mean)+6,name);
 minZ=Math.min(minZ,z);maxZ=Math.max(maxZ,z);stages[stage]++;hits+=output.candidates.length;
}
assert.deepEqual(stages,{pinning:33,round1:46,round2:39});assert.equal(hits,16);
console.log(JSON.stringify({status:'passed',nativeEnvelopes:rows.length,stages,candidates: hits,
 gateCountZScore:{min:minZ,max:maxZ},schema:3,registeredInMemoryOnly:true,enrolled:false,
 limits:['No new GPU execution, CPU cryptographic verification, registry publication or deployment',
 'Pinned served consumer checks gate accounting bounds; six-sigma sanity was checked here separately']}));
