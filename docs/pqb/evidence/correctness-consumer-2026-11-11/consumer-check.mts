
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
