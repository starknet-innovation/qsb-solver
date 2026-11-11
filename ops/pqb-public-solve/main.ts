import { readFileSync } from 'node:fs';
import { solve } from './controller';
const [config,input,out]=process.argv.slice(2);
if(!config||!input||!out)throw Error('Expected CONFIG PUBLIC_INPUT NEW_RESULT_DIRECTORY');
solve(JSON.parse(readFileSync(config,'utf8')),JSON.parse(readFileSync(input,'utf8')),out)
  .catch(error=>{console.error(String(error));process.exitCode=1;});
