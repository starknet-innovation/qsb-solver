// Local public-only export for a second implementation's verification.
import { readFileSync, writeFileSync, existsSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { pqbPacket, pqbProblem } from 'consumer/src/lib/pqb';
const [checkpoint, output] = process.argv.slice(2);
if (!checkpoint || !output || existsSync(output)) throw Error('New output path required');
const state = JSON.parse(readFileSync(checkpoint, 'utf8'));
const input = JSON.parse(readFileSync(join(dirname(checkpoint), 'input.json'), 'utf8'));
// A re-pin abandons earlier hits but keeps them in state.solutions as history. Only the chain the job
// currently holds is exported: per stage, the latest hit whose candidate is the job's selected one.
const keys: Record<string, string> = { pinning: 'pinning', round1: 'round0', round2: 'round1' };
const chosen = state.job.solution?.pqb ?? {};
const current = Object.keys(keys).flatMap(stage => {
  const hit = state.solutions.findLast((s: any) => s.stage === stage && s.checked.candidate === chosen[keys[stage]]);
  if (chosen[keys[stage]] !== undefined && !hit) throw Error('Selected candidate has no recorded hit: ' + stage);
  return hit ? [hit] : [];
});
if (!current.length) throw Error('No currently selected solution to export');
const records = current.map((solution: any) => {
  const stage = ['pinning', 'round1', 'round2'].indexOf(solution.stage);
  if (stage < 0) throw Error('Unsupported stage');
  const packet = pqbPacket(input.publicStateJson, input.manifest, stage, state.job.solution);
  return { stage: solution.stage, jobId: solution.jobId, candidate: solution.checked.candidate,
    packet, problem: pqbProblem(input.publicStateJson, input.manifest, stage, state.job.solution) };
});
writeFileSync(output, JSON.stringify({ format: 'qsb-public-upstream-crosscheck-v1', records }, null, 2) + '\n', { flag: 'wx' });
