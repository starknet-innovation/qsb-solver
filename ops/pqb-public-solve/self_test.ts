// Simulated provider; real consumer schemas, input/output and CPU-negative checks.
import assert from 'node:assert/strict';
import { readFileSync, mkdtempSync, existsSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { solve, sha } from './controller';
import { pqbWorkRange } from 'consumer/server/pqb-search';
const input=JSON.parse(readFileSync(process.argv[2],'utf8'));
const base=mkdtempSync(tmpdir()+'/qsb-pqb-controller-test-');
const config={format:'qsb-pqb-public-solve-v1',deadline:Math.floor(Date.now()/1000)+1800,
  workers:16,maxUnits:1,maxReservedGpuSeconds:900,solverCommit:'a'.repeat(40),binarySha256:'b'.repeat(64),
  image:'123456789012.dkr.ecr.eu-west-1.amazonaws.com/qsb-pqb-solve-12345678@sha256:'+'c'.repeat(64),queue:'test',definition:'test',bucket:'test'};
async function main(){
let known:any,knownProvider:any;
for(const mode of ['empty','unknown','wrong-context']){
  const out=base+'/'+mode;let posts=0,prepares=0;let payload:any;
  const provider={prepareRun:async(_image:string,p:any)=>{
    prepares++;payload=p;
    const submission=async()=>{
      posts++;const state=JSON.parse(readFileSync(out+'/state.json','utf8'));
      assert.equal(state.job.gpuBudgetReservedSeconds,900);assert.equal(state.slots.length,1);
      assert.equal(state.slots[0].id,undefined);assert.equal(state.slots[0].identity.inputSha256,sha(JSON.stringify({input:p})));
      if(mode==='empty'){known=structuredClone(state);known.slots[0].id='00000000-0000-4000-8000-000000000001';}
      if(mode==='unknown')throw Error('Simulated uncertain POST');
      return {id:'00000000-0000-4000-8000-000000000001'};
    };
    return Object.assign(submission,{identity:{jobName:'qsb-00000000-0000-4000-8000-000000000001',
      queue:config.queue,definition:config.definition,inputSha256:sha(JSON.stringify({input:p}))}});
  },status:async()=>({status:'COMPLETED',executionTime:1000,output:{status:'completed',stage:'pinning',
    manifestHash:mode==='wrong-context'?'0'.repeat(64):payload.manifestHash,attempt:0,kernelCommit:config.solverCommit,
    checkpoint:'range-complete',searchVersion:'pqb-ranked-v2',verified:false,workRange:pqbWorkRange('pinning',0),
    trials:pqbWorkRange('pinning',0).count*72,gateHits:0,candidates:[]}}),cancel:async()=>{}};
  await assert.rejects(()=>solve(config,input,out,provider,0));
  if(mode==='empty')knownProvider=provider;
  const state=JSON.parse(readFileSync(out+'/state.json','utf8'));
  assert.equal(posts,1);assert.equal(prepares,1);assert.equal(state.job.gpuBudgetReservedSeconds,900);
  assert.equal(state.status,mode==='unknown'?'submission-uncertain':'failed');
  if(mode==='empty')assert.ok(existsSync(out+'/jobs/00000000-0000-4000-8000-000000000001-cpu.json'));
  await assert.rejects(()=>solve(config,input,out,provider,0),/One-shot/);assert.equal(posts,1);
}
await assert.rejects(()=>solve(config,input,base+'/handover',knownProvider,0,known),/reservation exhausted/);
const handed=JSON.parse(readFileSync(base+'/handover/state.json','utf8'));
assert.equal(handed.job.gpuSubmissions,1);assert.equal(handed.job.gpuBudgetReservedSeconds,900);
assert.equal(handed.handover.id,known.slots[0].id);assert.equal(handed.startedAt,known.startedAt);
const unknown=structuredClone(known);delete unknown.slots[0].id;
await assert.rejects(()=>solve(config,input,base+'/unknown-handover',knownProvider,0,unknown),/Only one known/);
console.log('Controller failure/identity/reservation/one-shot and known-preflight handover cases passed; no AWS calls');
}
main().catch(error=>{console.error(error);process.exitCode=1;});
