"""Check a HOLD proposal with a clean pinned qsb-app, without enrolling or deploying.

Replays retained native result envelopes through the actual consumer schemas/ranges.
This is compatibility evidence, not a new GPU or independent cryptographic attestation.
"""
import argparse
import io
import json
import os
from pathlib import Path
import subprocess
import tarfile
from pqb_descriptor import ROOT, evidence_bytes, prepare, sha

TS = r'''
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
'''


ARCHIVE = 's3-objects.tar.gz'


def replay_rows(evidence, manifest):
    """Native result envelopes from the archive the manifest binds, member for member."""
    listed = [row for row in manifest['files'] if row['path'] == ARCHIVE]
    if len(listed) != 1:
        raise ValueError('Replay archive is not a manifest entry')
    raw = evidence_bytes(evidence, ARCHIVE, listed[0])
    inventory = {row['path']: row for row in manifest['archiveMembers'][ARCHIVE]}
    if len(inventory) != len(manifest['archiveMembers'][ARCHIVE]):
        raise ValueError('Duplicate archive inventory path')
    rows, seen = [], set()
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        for member in archive:
            if not member.isfile() or member.name in seen or member.name not in inventory:
                raise ValueError('Archive member outside the inventory: ' + member.name)
            seen.add(member.name)
            data = archive.extractfile(member).read()
            row = inventory[member.name]
            if len(data) != row['bytes'] or sha(data) != row['sha256']:
                raise ValueError('Archive member differs from the inventory: ' + member.name)
            if member.name.startswith('s3/outputs/') and member.name.endswith('.json') and not member.name.endswith('.collection.json'):
                rows.append(dict(name=member.name, envelope=json.loads(data)))
    if seen != set(inventory):
        raise ValueError('Archive omits inventory members')
    return rows


def check(app, commit, evidence, proposal_path, out):
    app, evidence, proposal_path, out = (p.resolve() for p in (app, evidence, proposal_path, out))
    if out.is_relative_to(ROOT) or out.is_relative_to(app):
        raise ValueError('Keep working evidence outside both checkouts')
    def git(*args):
        return subprocess.check_output(['git', '-C', str(app), *args], text=True).strip()
    if git('rev-parse', 'HEAD') != commit or git('status', '--porcelain'):
        raise ValueError('Consumer must be clean and pinned')
    proposal = json.loads(proposal_path.read_bytes())
    if proposal != prepare(evidence, proposal['binding']['reviewedSourceCommit']):
        raise ValueError('Proposal differs from verified evidence/source')
    if (app / 'contracts/pqb-ranked-v2.json').read_bytes() != subprocess.check_output([
            'git', '-C', str(ROOT), 'show', proposal['solver']['solverCommit'] + ':contracts/pqb-ranked-v2.json']):
        raise ValueError('Consumer contract differs')
    manifest_raw = (evidence / 'manifest.json').read_bytes()
    if sha(manifest_raw) != proposal['binding']['evidenceManifestSha256']:
        raise ValueError('Evidence manifest changed after the proposal check')
    rows = replay_rows(evidence, json.loads(manifest_raw))
    out.mkdir(parents=True, exist_ok=False)
    (out / 'check.mts').write_text(TS)
    (out / 'input.json').write_text(json.dumps(dict(proposal=proposal, rows=rows)))
    result = subprocess.run([str(app / 'node_modules/.bin/tsx'), str(out / 'check.mts'), str(app), str(out / 'input.json')],
                            cwd=app, env={**os.environ, 'QSB_NETWORK': 'mainnet'}, capture_output=True, text=True, timeout=120)
    (out / 'stdout').write_text(result.stdout)
    (out / 'stderr').write_text(result.stderr)
    receipt = dict(format='qsb-pqb-release-compatibility-v1', status='failed', consumerCommit=commit,
                   consumerTree=git('rev-parse', 'HEAD^{tree}'), node=subprocess.check_output(['node', '--version'], text=True).strip(),
                   proposalSha256=sha(proposal_path.read_bytes()), harnessSha256=sha(Path(__file__).read_bytes()),
                   typescriptSha256=sha(TS.encode()), evidenceManifestSha256=sha(manifest_raw),
                   consumerLockSha256=sha((app / 'package-lock.json').read_bytes()))
    if result.returncode == 0:
        receipt.update(json.loads(result.stdout))
    else:
        receipt['error'] = result.stderr
    (out / 'result.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))
    return result.returncode


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('consumer', type=Path)
    parser.add_argument('commit')
    parser.add_argument('evidence', type=Path)
    parser.add_argument('proposal', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    raise SystemExit(check(args.consumer, args.commit, args.evidence, args.proposal, args.output))
