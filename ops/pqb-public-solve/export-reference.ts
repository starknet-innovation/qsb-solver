// Local public-only export for a second implementation's verification.
import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { pqbPacket, pqbProblem } from 'consumer/src/lib/pqb';
const [checkpoint, output] = process.argv.slice(2);
if (!checkpoint || !output || existsSync(output)) throw Error('New output path required');
const state = JSON.parse(readFileSync(checkpoint, 'utf8'));
const input = JSON.parse(readFileSync(join(dirname(checkpoint), 'input.json'), 'utf8'));
const records = state.solutions.map((solution: any) => {
  const stage = ['pinning', 'round1', 'round2'].indexOf(solution.stage);
  if (stage < 0) throw Error('Unsupported stage');
  const packet = pqbPacket(input.publicStateJson, input.manifest, stage, state.job.solution);
  return { stage: solution.stage, jobId: solution.jobId, candidate: solution.checked.candidate,
    packet, problem: pqbProblem(input.publicStateJson, input.manifest, stage, state.job.solution) };
});
writeFileSync(output, JSON.stringify({ format: 'qsb-public-upstream-crosscheck-v1', records }, null, 2) + '\n', { flag: 'wx' });
