import { readFileSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { solve, sha } from './controller';
const [config,input,out,preflight]=process.argv.slice(2);
if(!config||!input||!out)throw Error('Expected CONFIG PUBLIC_INPUT NEW_RESULT_DIRECTORY');
let previous;
if(preflight){
  const raw=readFileSync(preflight,'utf8');previous=JSON.parse(raw);previous.checkpointFileSha256=sha(raw);
  previous.completedSlots=previous.observations.map((x:any)=>{
    if(!/^[a-f0-9-]{36}$/.test(x.id??''))throw Error('Invalid observed job ID');
    return JSON.parse(readFileSync(join(dirname(preflight),'jobs',x.id+'.json'),'utf8')).slot;
  });
}
solve(JSON.parse(readFileSync(config,'utf8')),JSON.parse(readFileSync(input,'utf8')),out,undefined,10000,
  previous)
  .catch(error=>{console.error(String(error));process.exitCode=1;});
