import { pqbPacket, pqbProblem } from 'consumer/src/lib/pqb';

// The audit history also contains abandoned pinning/round solutions after re-pinning.
// Export only the current chain, in dependency order, under its current public context.
export function selectedRecords(state: any, input: any) {
  const selected = state.job.solution;
  if (!selected) return [];
  const stages = [['pinning', 'pinning'], ['round1', 'round0'], ['round2', 'round1']];
  const records = [];
  for (const [stage, key] of stages) {
    const candidate = selected.pqb?.[key];
    if (candidate === undefined) break;
    const solution = [...state.solutions].reverse().find(s => s.stage === stage && s.checked.candidate === candidate);
    if (!solution) throw Error('Selected solution missing from retained history');
    const index = records.length;
    records.push({ stage, jobId: solution.jobId, candidate,
      packet: pqbPacket(input.publicStateJson, input.manifest, index, selected),
      problem: pqbProblem(input.publicStateJson, input.manifest, index, selected) });
  }
  if (Object.keys(selected.pqb ?? {}).length !== records.length) throw Error('Incomplete selected solution chain');
  return records;
}
