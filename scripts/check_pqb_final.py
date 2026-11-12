"""Replay the final-image native archive through the pinned qsb-app CPU consumer.

No registry write, enrollment or deployment. The caller supplies the original archive's
independently collected SHA-256; results are never rewritten to a newer image identity.
"""
import argparse
import base64
import gzip
import json
import os
from pathlib import Path
import subprocess
from pqb_descriptor import ROOT, contract_hash, sha, source
from pqb_import import verify_runtime

STAGES = ('pinning', 'round0', 'round1')


def unique(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError('Duplicate archive/JSON key: ' + key)
        result[key] = value
    return result


def native_rows(raw, digest, solver, build):
    if sha(raw) != digest:
        raise ValueError('Original native archive hash mismatch')
    files = json.loads(gzip.decompress(raw), object_pairs_hook=unique)
    if not isinstance(files, dict) or any(not isinstance(v, str) or Path(k).is_absolute()
            or '..' in Path(k).parts for k, v in files.items()):
        raise ValueError('Unsafe native archive inventory')
    def read(name):
        return json.loads(files[name], object_pairs_hook=unique)
    imported = read('runtime-identity-check.json')
    if imported['status'] != 'passed' or imported['imageDigest'] != build['identity']['imageDigest'] \
            or imported['configDigest'] != build['identity']['configDigest']:
        raise ValueError('Imported runtime identity differs')
    verify_runtime(read('image.json')[0], build['config'])
    if files['exit-code.txt'].strip() != '0' or files['stage.txt'].strip() != 'all':
        raise ValueError('Host qualification did not succeed')
    all_units = read('unit/result.json')
    if all_units['status'] != 'passed' or [r['stage'] for r in all_units['stages']] != list(STAGES):
        raise ValueError('Incomplete native stages')
    commit = solver['solverCommit']
    contract = source(commit, 'contracts/pqb-ranked-v2.json')
    ranges_raw = source(commit, 'worker/pqb/pqb_ranges.py')
    if contract_hash(contract, ranges_raw) != solver['searchContract']:
        raise ValueError('Descriptor differs from committed contract')
    ranges = {}
    exec(compile(ranges_raw, 'committed-pqb-ranges.py', 'exec'), ranges)
    rows = []
    for stage, summary in zip(STAGES, all_units['stages']):
        prefix = 'unit/' + stage + '/'
        if summary['status'] != 'passed' or summary['resultPath'] != stage + '/result.json' \
                or sha(files[prefix+'result.json'].encode()) != summary['resultSha256']:
            raise ValueError('Native stage summary differs')
        row = read(prefix+'result.json')
        if row['status'] != 'passed' or row['stage'] != stage or row['workerTimeoutSeconds'] != 840 \
                or row['contractSha256'] != solver['searchContract'] \
                or row['binding'] != build['binding'] or row['buildReceipt'] != build['receipt'] \
                or row['image'] != build['identity'] \
                or solver['image'].split('@')[1] != row['image']['imageDigest']:
            raise ValueError('Native artifact identity differs')
        for name, digest in row['files'].items():
            if sha(files[prefix+name].encode()) != digest:
                raise ValueError('Native retained file hash mismatch: ' + name)
        actual = {name[len(prefix):] for name in files if name.startswith(prefix)
                  and Path(name).name != 'result.json'}
        if actual != set(row['files']):
            raise ValueError('Native retained inventory differs')
        for name in ('pqb_handler.py', 'pqb_ranges.py'):
            if row['binding']['files'][name] != sha(source(commit, 'worker/pqb/'+name)):
                raise ValueError('Installed worker Python differs from committed source')
        if row['binding']['files']['grind'] != row['buildReceipt']['binarySha256']:
            raise ValueError('Native binary binding differs')
        if len(row['correctness']) != 13 or not all(c['pass'] for c in row['correctness']):
            raise ValueError('Native independent small cases incomplete')
        unit = row['unit']
        attempt = max(range(1 if stage == 'pinning' else ranges['unit_count'](stage)),
                      key=lambda a:ranges['work_range'](stage, a)['count'])
        if not unit['pass'] or not unit['nativeDevice'] or not unit['gateCountSanity'] \
                or unit['jobSeconds'] >= 840 or unit['attempt'] != attempt \
                or unit['workRange'] != ranges['work_range'](stage, attempt):
            raise ValueError('Largest native unit did not meet the fixed plan')
        response = read(prefix+'worker-result.json')
        request = read(prefix+'request.json')['input']
        fixture = 'pin' if stage == 'pinning' else stage
        problem = source(commit, 'research/pqb-ranked/tests/fixtures/'+fixture+'.txt').replace(
            b'gate_bits 12\n', b'gate_bits 24\n')
        if response != unit['workerResult'] or response['status'] != 'completed' \
                or request['stage'] != stage or request['attempt'] != attempt \
                or request['problemSha256'] != sha(problem) \
                or base64.b64decode(request['problemBase64'], validate=True) != problem \
                or files[prefix+'work/P.txt'].encode() != problem:
            raise ValueError('Native request/result/problem differ')
        packet = source(commit, 'research/pqb-ranked/tests/fixtures/'+fixture+'.packet.json').decode()
        rows.append(dict(stage=stage, response=response, packet=packet, problem=problem.decode(),
                         jobSeconds=unit['jobSeconds'], workerSeconds=unit['workerSeconds']))
    return rows


TS = r'''
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {pathToFileURL} from 'node:url';
const [app,input]=process.argv.slice(2);
const {proposal,rows}=JSON.parse(readFileSync(input,'utf8'));
const mod=await import(pathToFileURL(app+'/src/lib/provenance.ts').href);
const {checkedOutput,assertSolverRuntime}=await import(pathToFileURL(app+'/server/search-protocol.ts').href);
const {parsePacket,problemFromPacket,problemTxt,HitChecker}=await import(pathToFileURL(app+'/src/pqb-core/grind.ts').href);
const solver=mod.externalSolverDescriptorSchema.parse(proposal.solver);
assertSolverRuntime(solver);mod.assertPaidSolverContract(solver);
assert.equal(mod.solverRegistry([solver]).get(solver.id),mod.canonical(solver));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse(proposal));
assert.throws(()=>mod.solverRegistry([solver,solver]));
assert.throws(()=>mod.solverRegistry([{...solver,searchContract:'0'.repeat(64)}]));
assert.throws(()=>mod.externalSolverDescriptorSchema.parse({...solver,generatorCommit:'0'.repeat(40)}));
assert.throws(()=>mod.solverRelease(solver.id),/UnsupportedSolverRelease/);
const results=[];
for(const row of rows){
 const raw=row.response,stage=raw.stage==='round0'?'round1':raw.stage==='round1'?'round2':'pinning';
 const job:any={stage,manifestHash:raw.manifestHash};
 const {output,range}=checkedOutput(raw,solver,job,raw.attempt);
 assert.equal(output.status,'completed');
 assert.throws(()=>checkedOutput({...raw,kernelCommit:'0'.repeat(40)},solver,job,raw.attempt));
 assert.throws(()=>checkedOutput({...raw,protocol:'qsb-v1'},solver,job,raw.attempt));
 assert.throws(()=>checkedOutput({...raw,workRange:{...raw.workRange,start:'1'}},solver,job,raw.attempt));
 const packet=parsePacket(row.packet),prob=problemFromPacket(packet,24);
 assert.equal(problemTxt(prob),row.problem);
 const checker=new HitChecker(packet,prob,24);
 for(const hit of output.candidates)checker.check(hit);
 const mean=raw.trials/2**24;
 assert.ok(Math.abs(raw.gateHits-mean)<=6*Math.sqrt(mean)+6);
 results.push({stage:row.stage,attempt:raw.attempt,candidates:output.candidates.length,
   consumerChecks:checker.stats(),workerSeconds:row.workerSeconds,jobSeconds:row.jobSeconds});
}
console.log(JSON.stringify({status:'passed',schema:3,stages:results,enrolled:false,
  publicationVerified:false,scope:'Fresh exact-image native envelopes and CPU cryptographic checks',
  limits:['No new complete solve, served Step Functions, wallet, consensus, miner or broadcast test',
  'Six-sigma gate sanity checked separately; served consumer only enforces accounting bounds']}));
'''


def check(app, commit, archive, digest, proposal_path, out, artifacts):
    app, out = app.resolve(), out.resolve()
    if out.is_relative_to(ROOT) or out.is_relative_to(app):
        raise ValueError('Keep working receipts outside both checkouts')
    def git(*args):
        return subprocess.check_output(['git','-C',str(app),*args],text=True).strip()
    if git('rev-parse','HEAD') != commit or git('status','--porcelain'):
        raise ValueError('Consumer must be clean and pinned')
    proposal = json.loads(proposal_path.read_bytes())
    solver = proposal['solver']
    if solver['solverCommit'] != solver['kernelCommit'] or proposal['status'] != 'HOLD':
        raise ValueError('Unexpected descriptor/source')
    if (app/'contracts/pqb-ranked-v2.json').read_bytes() != source(solver['solverCommit'],'contracts/pqb-ranked-v2.json'):
        raise ValueError('Consumer contract differs')
    build = {key:json.loads((artifacts/name).read_bytes()) for key,name in (
        ('identity','oci-identity.json'),('config','image-config.json'),
        ('binding','binding.json'),('receipt','build-receipt.json'))}
    if 'ghcr.io/starknet-innovation/qsb-solver@'+build['identity']['imageDigest'] != solver['image']:
        raise ValueError('Descriptor differs from build artifact')
    rows = native_rows(archive.read_bytes(), digest, solver, build)
    out.mkdir(parents=True,exist_ok=False)
    (out/'check.mts').write_text(TS)
    (out/'input.json').write_text(json.dumps(dict(proposal=proposal,rows=rows)))
    result = subprocess.run([str(app/'node_modules/.bin/tsx'),str(out/'check.mts'),str(app),str(out/'input.json')],
        cwd=app,env={**os.environ,'QSB_NETWORK':'mainnet'},capture_output=True,text=True,timeout=120)
    (out/'stdout').write_text(result.stdout);(out/'stderr').write_text(result.stderr)
    receipt = dict(format='qsb-pqb-final-consumer-v1',status='failed',consumerCommit=commit,
        consumerTree=git('rev-parse','HEAD^{tree}'),archiveSha256=digest,proposalSha256=sha(proposal_path.read_bytes()),
        harnessSha256=sha(Path(__file__).read_bytes()),typescriptSha256=sha(TS.encode()),
        buildMetadataSha256={name:sha((artifacts/name).read_bytes()) for name in
            ('SHA256SUMS','oci-identity.json','image-config.json','binding.json','build-receipt.json')},
        consumerLockSha256=sha((app/'package-lock.json').read_bytes()))
    if result.returncode == 0:
        receipt.update(json.loads(result.stdout))
    else:
        receipt['error'] = result.stderr
    (out/'result.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
    return result.returncode


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('consumer',type=Path);p.add_argument('commit');p.add_argument('archive',type=Path)
    p.add_argument('sha256');p.add_argument('proposal',type=Path);p.add_argument('output',type=Path)
    p.add_argument('--build-artifacts',type=Path,required=True,
        help='Exact independently attestation-verified build artifact directory')
    a=p.parse_args()
    raise SystemExit(check(a.consumer,a.commit,a.archive,a.sha256,a.proposal,a.output,a.build_artifacts))
