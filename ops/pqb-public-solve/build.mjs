// This is a local bundler; it installs nothing and allocates no hardware.
import { createRequire } from 'node:module';
import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { writeFileSync, readFileSync, mkdirSync } from 'node:fs';
import { createHash } from 'node:crypto';
const [app,commit,out]=process.argv.slice(2).map((v,i)=>i===1?v:resolve(v));
if(execFileSync('git',['-C',app,'rev-parse','HEAD'],{encoding:'utf8'}).trim()!==commit
 ||execFileSync('git',['-C',app,'status','--porcelain'],{encoding:'utf8'}).trim())throw Error('Consumer checkout must be clean and pinned');
const require=createRequire(app+'/package.json');const {build}=require('esbuild');
const lock=JSON.parse(readFileSync('ops/pqb-public-solve/consumer-lock.json','utf8'));
if(lock.commit!==commit)throw Error('Consumer lock commit differs');
for(const [name,want] of Object.entries(lock.files))
 if(createHash('sha256').update(readFileSync(app+'/'+name)).digest('hex')!==want)throw Error('Consumer byte mismatch: '+name);
mkdirSync(out,{recursive:false});
const result=await build({entryPoints:['ops/pqb-public-solve/main.ts'],bundle:true,platform:'node',format:'cjs',
 outfile:out+'/controller.cjs',alias:{consumer:app},define:{'import.meta.env':'undefined'},metafile:true});
await build({entryPoints:['ops/pqb-public-solve/self_test.ts'],bundle:true,platform:'node',format:'cjs',
 outfile:out+'/self-test.cjs',alias:{consumer:app},define:{'import.meta.env':'undefined'}});
const reference=await build({entryPoints:['ops/pqb-public-solve/export-reference.ts'],bundle:true,platform:'node',format:'cjs',
 outfile:out+'/export-reference.cjs',alias:{consumer:app},define:{'import.meta.env':'undefined'},metafile:true});
const referenceInputs=Object.fromEntries(Object.keys(reference.metafile.inputs).sort().map(p=>[p,createHash('sha256').update(readFileSync(p)).digest('hex')]));
const hashes=Object.fromEntries(Object.keys(result.metafile.inputs).sort().map(p=>[p,createHash('sha256').update(readFileSync(p)).digest('hex')]));
writeFileSync(out+'/build-receipt.json',JSON.stringify({consumerCommit:commit,node:process.version,inputs:hashes,
 controllerSha256:createHash('sha256').update(readFileSync(out+'/controller.cjs')).digest('hex'),referenceInputs,
 referenceExportSha256:createHash('sha256').update(readFileSync(out+'/export-reference.cjs')).digest('hex')},null,2)+'\n');
