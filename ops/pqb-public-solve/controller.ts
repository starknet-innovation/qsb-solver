// Public synthetic validation, not a served app coordinator or enrolled release.
import { createHash } from 'node:crypto';
import { mkdirSync, writeFileSync, renameSync, openSync, fsyncSync, closeSync, readFileSync, existsSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { AwsBatch } from 'consumer/server/aws-batch';
import { pqbReference } from 'consumer/server/pqb-reference';
import { checkedOutput, workerInput, assertSolverRuntime } from 'consumer/server/search-protocol';
import { applyVerifiedHit } from 'consumer/server/candidate-output';
import { pqbWorkRange } from 'consumer/server/pqb-search';
import { nextGpuReservation, gpuSpendLimits } from 'consumer/server/gpu-spend';
import { withdrawalSchema, canonicalManifest } from 'consumer/src/lib/model';
import { pqbPublicStateSchema } from 'consumer/src/lib/pqb';
import { PQB_GENERATOR_COMMIT } from 'consumer/src/lib/pqb-identity';
import { solverSearchContracts } from 'consumer/src/lib/search-contracts.generated';
import { assertPaidSolverContract } from 'consumer/src/lib/provenance';

export const sha = (value: string) => createHash('sha256').update(value).digest('hex');
const active = (s: string) => ['IN_QUEUE','IN_PROGRESS'].includes(s);
export function save(path: string, value: unknown) {
  const temp=path+'.tmp'; writeFileSync(temp,JSON.stringify(value,null,2)+'\n',{mode:0o600});
  const fd=openSync(temp,'r'); fsyncSync(fd); closeSync(fd); renameSync(temp,path);
  const parent=openSync(dirname(path),'r');fsyncSync(parent);closeSync(parent);
}
type Slot = {stage:string; epoch:number; attempt:number; identity:any; id?:string; context:any; cancellation?:string; cancellationConfirmed?:string};
export async function solve(config: any, publicInput: any, directory: string, injectedProvider?: any, pollMs=10000, preflight?: any) {
  const dir=resolve(directory);
  if(existsSync(dir)) throw Error('One-shot result directory already exists');
  if(config.format!=='qsb-pqb-public-solve-v1' || !Number.isSafeInteger(config.deadline)
    || config.deadline*1000<=Date.now() || config.deadline*1000>Date.now()+6*3600000
    || !Number.isInteger(config.workers) || config.workers<1 || config.workers>gpuSpendLimits.workersMax
    || !Number.isInteger(config.maxUnits) || config.maxUnits<1 || config.maxUnits>600
    || config.maxReservedGpuSeconds!==config.maxUnits*900
    || !/^[a-f0-9]{40}$/.test(config.solverCommit)
    || !/^[a-f0-9]{64}$/.test(config.binarySha256)
    || !/^\d{12}\.dkr\.ecr\.eu-west-1\.amazonaws.com\/qsb-pqb-solve-[a-z0-9-]+@sha256:[a-f0-9]{64}$/.test(config.image))
    throw Error('Invalid fixed campaign limits or immutable image identity');
  if(Object.keys(publicInput).sort().join(',')!=='manifest,publicStateJson') throw Error('Public input fields invalid');
  pqbPublicStateSchema.parse(JSON.parse(publicInput.publicStateJson));
  const manifest=withdrawalSchema.parse(publicInput.manifest);
  const selected:any={schemaVersion:3,id:'public-validation-only',protocol:'pqb-v1',
    generatorCommit:PQB_GENERATOR_COMMIT,searchVersion:'pqb-ranked-v2',
    searchContract:solverSearchContracts['pqb-v1'],solverRepository:'https://github.com/starknet-innovation/qsb-solver',
    solverCommit:config.solverCommit,kernelCommit:config.solverCommit,image:config.image};
  assertSolverRuntime(selected); assertPaidSolverContract(selected);
  const job:any={manifest,manifestHash:sha(JSON.stringify(canonicalManifest(manifest))),stage:'pinning',attempt:0,
    computeSeconds:0,gpuSubmissions:0,gpuBudgetReservedSeconds:0,solver:{descriptor:selected}};
  const state:any={format:'qsb-pqb-public-solve-state-v1',status:'running',startedAt:new Date().toISOString(),
    config,configSha256:sha(JSON.stringify(config)),publicInputSha256:sha(JSON.stringify(publicInput)),
    job,epoch:0,nextAttempt:0,slots:[] as Slot[],observations:[],solutions:[],notes:[
      'Private validation image; not an enrolled or served release',
      'Actual consumer AwsBatch, input/output checks, stage transitions and CPU reference; development orchestration',
      'No Step Functions, wallet, signing, consensus execution, funded outputs or broadcast in this assessment']};
  if(preflight){
    const count=preflight.job?.gpuSubmissions;
    const prior=[...(preflight.slots??[]),...(preflight.completedSlots??[])];
    const ids=prior.map((s:any)=>s.id),attempts=prior.map((s:any)=>s.attempt).sort((a:number,b:number)=>a-b);
    if(preflight.format!=='qsb-pqb-public-solve-state-v1'||preflight.status!=='running'
      ||preflight.configSha256!==state.configSha256||preflight.publicInputSha256!==state.publicInputSha256
      ||preflight.epoch!==0||!Number.isInteger(count)||count<1||count>config.maxUnits
      ||preflight.nextAttempt!==count||prior.length!==count||new Set(ids).size!==count
      ||preflight.slots.length>config.workers||preflight.solutions.length!==0
      ||(preflight.completedSlots??[]).length!==preflight.observations.length
      ||preflight.observations.some((x:any)=>x.status!=='COMPLETED'||x.stage!=='pinning')
      ||preflight.job.gpuBudgetReservedSeconds!==900*count||preflight.job.stage!=='pinning'
      ||attempts.some((x:number,i:number)=>x!==i))
      throw Error('Known initial pinning phase required; no unknown submissions or changed limits');
    const exported=pqbReference({action:'export',publicStateJson:publicInput.publicStateJson,manifest,stage:'pinning'});
    for(const slot of prior){
      if(slot.stage!=='pinning'||slot.epoch!==0||slot.cancellation||!/^[a-f0-9-]{36}$/.test(slot.id??'')
        ||slot.identity.queue!==config.queue||slot.identity.definition!==config.definition
        ||slot.context.manifestHash!==job.manifestHash||JSON.stringify(slot.context.solver.descriptor)!==JSON.stringify(selected)
        ||slot.identity.inputSha256!==sha(JSON.stringify({input:workerInput(selected,job,slot.attempt,exported)})))
        throw Error('Known pinning request/input identity differs');
    }
    job.gpuSubmissions=count;job.gpuBudgetReservedSeconds=900*count;state.nextAttempt=count;
    state.slots=structuredClone(prior);state.startedAt=preflight.startedAt;
    state.controllerStartedAt=new Date().toISOString();state.handover={stateSha256:sha(JSON.stringify(preflight)),
      checkpointFileSha256:preflight.checkpointFileSha256,ids,
      reason:'Known requests retained without replay, refund or deadline change; all completed outputs rechecked'};
  }
  mkdirSync(dir,{recursive:false}); mkdirSync(dir+'/jobs'); save(dir+'/input.json',publicInput);
  const persist=()=>save(dir+'/state.json',state); persist();
  const provider=injectedProvider??new AwsBatch(config.queue,config.definition,config.bucket);
  const reference=(context:any,action:string,candidates?:string[])=>pqbReference({
    action,publicStateJson:publicInput.publicStateJson,manifest,stage:context.stage,
    ...(context.solution?{solution:context.solution}:{}),...(candidates?{candidates}:{})});
  const cancel=async(slot:Slot)=>{
    // `cancellation` records the intent, before the call; `cancellationConfirmed` that the provider accepted it.
    // A rejected or lost cancel leaves it unconfirmed, so the next pass and the failure path retry it (it is idempotent).
    if(slot.id&&!slot.cancellationConfirmed){
      if(!slot.cancellation){slot.cancellation=new Date().toISOString();persist();}
      await provider.cancel(slot.id);slot.cancellationConfirmed=new Date().toISOString();persist();
    }
  };
  try {
    while(true){
      if(Date.now()>=config.deadline*1000-60000) throw Error('Fixed campaign deadline reached');
      const observed=await Promise.all((state.slots as Slot[]).filter(s=>s.id).map(async slot=>({slot,result:await provider.status(slot.id,slot.identity)})));
      for(const {slot,result} of observed){
        if(active(result.status)) {if(slot.epoch!==state.epoch)await cancel(slot);continue;}
        save(dir+'/jobs/'+slot.id+'.json',{slot,result});
        if(result.status==='COMPLETED'){
          const {output,range}=checkedOutput(result.output,selected,slot.context,slot.attempt);
          if(new Set(output.candidates).size!==output.candidates.length)throw Error('Duplicate candidate');
          const cpu=reference(slot.context,'verify',output.candidates);
          save(dir+'/jobs/'+slot.id+'-cpu.json',{checked:cpu,range});
          job.computeSeconds+=(result.executionTime??0)/1000;
          if(output.status!=='completed'||output.checkpoint!=='range-complete')throw Error('Incomplete worker result');
          // A worker that skipped trials but reported the contractual z-block count would still show too few
          // 24-bit gate hits. Trials are computed here from the checked range, not taken from the worker;
          // the bound is the full-unit harness's (6 sigma + 6).
          const tries=({pinning:72,round1:192,round2:64} as Record<string,number>)[slot.stage];
          const gateMean=Number(range.count)*tries/2**24;
          // read from the raw worker result: the consumer's parsed output keeps only its own schema's fields
          const gateHits=(result.output as any)?.gateHits;
          if(!Number.isSafeInteger(gateHits)||!(Math.abs(gateHits-gateMean)<=6*Math.sqrt(gateMean)+6))
            throw Error('Gate-hit count inconsistent with the unit size; range not credited');
          if(slot.epoch===state.epoch){
            if(cpu.valid===true){
              const before=structuredClone(job);applyVerifiedHit(job,cpu,range,slot.attempt);
              state.solutions.push({stage:before.stage,attempt:slot.attempt,jobId:slot.id,checked:cpu,range});
              state.epoch++;state.nextAttempt=0;job.attempt=0;
              console.log(JSON.stringify({event:'stage-solved',stage:before.stage,next:job.stage,jobId:slot.id}));
            } else if(output.candidates.length&&cpu.derOnly!==true)throw Error('Independent CPU rejection requires review');
          }
        } else if(!slot.cancellation) throw Error('Unexpected Batch terminal failure: '+result.status);
        state.observations.push({id:slot.id,stage:slot.stage,attempt:slot.attempt,status:result.status,
          timing:result.timing,executionTime:result.executionTime,cancelled:Boolean(slot.cancellation)});
        state.slots=state.slots.filter((s:Slot)=>s!==slot);persist();
      }
      if(state.slots.some((s:Slot)=>!s.id))throw Error('Uncertain submission; never resubmit');
      for(const slot of state.slots as Slot[])if(slot.epoch!==state.epoch)await cancel(slot);
      const draining=state.slots.some((s:Slot)=>s.epoch!==state.epoch);
      if(job.stage==='verification'&&!state.slots.length){
        for(const [stage,key] of [['pinning','pinning'],['round1','round0'],['round2','round1']]){
          const cpu=reference({...job,stage},'verify',[job.solution.pqb[key]]);
          if(cpu.valid!==true||cpu.candidate!==job.solution.pqb[key])throw Error('Final independent verification failed');
        }
        state.status='solved-public';job.status='awaiting_authorization';state.finishedAt=new Date().toISOString();persist();
        console.log(JSON.stringify({event:'solved-public',submissions:job.gpuSubmissions,computeSeconds:job.computeSeconds}));return state;
      }
      let exhausted=false;
      const capacity=state.observations.length===0?1:config.workers;
      while(!draining&&job.stage!=='verification'&&state.slots.length<capacity){
        try{pqbWorkRange(job.stage,state.nextAttempt);}catch(error){
          if(!(error instanceof Error)||!error.message.includes('exhausted'))throw error;
          exhausted=true;break;
        }
        if(Date.now()>config.deadline*1000-1200000)throw Error('Insufficient fixed-deadline margin for another submission');
        const reserved=nextGpuReservation(job,gpuSpendLimits.executionTimeoutMs);
        if(job.gpuSubmissions>=config.maxUnits||reserved>config.maxReservedGpuSeconds
          ||reserved>gpuSpendLimits.maxJobGpuSeconds)throw Error('Campaign reservation exhausted');
        const context=structuredClone(job),attempt=state.nextAttempt;
        const parameters=reference(context,'export');
        const input=workerInput(selected,context,attempt,parameters);
        const submit=await provider.prepareRun(config.image,input);
        if(submit.identity.inputSha256!==sha(JSON.stringify({input})))throw Error('Prepared input digest differs');
        const slot:Slot={stage:job.stage,epoch:state.epoch,attempt,identity:submit.identity,context};
        state.slots.push(slot);job.gpuBudgetReservedSeconds=reserved;job.gpuSubmissions++;state.nextAttempt++;
        save(dir+'/jobs/'+submit.identity.jobName+'-intent.json',{slot,input,reserved});persist();
        // Persist identity and nonrefundable worst-case reservation before the one-shot paid POST.
        const sent=await submit();slot.id=sent.id;persist();
        console.log(JSON.stringify({event:'submitted',stage:slot.stage,attempt,jobId:slot.id,reservedSeconds:reserved}));
      }
      if(exhausted&&!state.slots.length){
        if(job.stage==='pinning')throw Error('Pinning search exhausted');
        state.epoch++;state.nextAttempt=job.pqbNextPinAttempt;job.stage='pinning';delete job.solution;persist();
        console.log(JSON.stringify({event:'repinning',attempt:state.nextAttempt}));
      }
      await new Promise(r=>setTimeout(r,pollMs));
    }
  }catch(error){
    state.status=state.slots.some((s:Slot)=>!s.id)?'submission-uncertain':'failed';state.error=String(error);persist();
    for(const slot of state.slots as Slot[])try{await cancel(slot);}catch(e){state.observations.push({cancellationError:String(e),id:slot.id});persist();}
    throw error;
  }
}
