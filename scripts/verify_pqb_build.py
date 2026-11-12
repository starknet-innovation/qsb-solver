"""Local-only verification of the exact hosted build; no registry push or cloud execution."""
import argparse,hashlib,json,pathlib,subprocess,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from pqb_oci import inspect
from pqb_descriptor import source,contract_hash,sha
WORKFLOW='starknet-innovation/qsb-solver/.github/workflows/pqb-qualify.yml'

def file_sha(path):
    with path.open('rb') as file:return hashlib.file_digest(file,'sha256').hexdigest()


def verify_policy(entries,commit,ref,run_id):
    if not entries:
        raise ValueError('No verified build provenance')
    for entry in entries:
        verified=entry['verificationResult']
        certificate=verified['signature']['certificate']
        expected={'sourceRepositoryURI':'https://github.com/starknet-innovation/qsb-solver',
                  'sourceRepositoryDigest':commit,'sourceRepositoryRef':ref,
                  'buildSignerURI':'https://github.com/'+WORKFLOW+'@'+ref,
                  'buildSignerDigest':commit,'runnerEnvironment':'github-hosted'}
        if any(certificate.get(k)!=v for k,v in expected.items()):
            raise ValueError('Verified signer/source/runtime policy differs')
        invocation='https://github.com/starknet-innovation/qsb-solver/actions/runs/'+str(run_id)+'/attempts/'
        if not certificate.get('runInvocationURI','').startswith(invocation):
            raise ValueError('Verified workflow run differs')

def verify(artifact,out,commit,ref,run_id):
    COMMIT,REF=commit,ref
    if not ref.startswith('refs/heads/codex/pqb-qualify-'):
        raise ValueError('Expected the dedicated qualification workflow source ref')
    source(COMMIT,'worker/pqb/Dockerfile')
    if out.resolve().is_relative_to(ROOT):
        raise ValueError('Keep working receipts outside the checkout')
    out.mkdir(exist_ok=False)
    policy=['--repo','starknet-innovation/qsb-solver','--signer-workflow',WORKFLOW,
            '--source-ref',REF,'--source-digest',COMMIT,'--deny-self-hosted-runners','--format','json']
    verifications={}
    for name in ['SHA256SUMS','image.oci.tar','image-manifest.json']:
        result=subprocess.run(['gh','attestation','verify',str(artifact/name),*policy],capture_output=True,text=True,timeout=180)
        (out/(name+'.verification.json')).write_text(result.stdout)
        (out/(name+'.verification.stderr')).write_text(result.stderr)
        result.check_returncode()
        verifications[name]=json.loads(result.stdout)
        verify_policy(verifications[name],COMMIT,REF,run_id)
    rows={}
    for line in (artifact/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1);path=artifact/name
        if name in rows or path.is_symlink() or pathlib.Path(name).is_absolute() or '..' in pathlib.Path(name).parts:
            raise ValueError('Unsafe or duplicated build asset')
        if file_sha(path)!=digest:raise ValueError('Build asset hash mismatch: '+name)
        rows[name]=digest
    actual={str(p.relative_to(artifact)) for p in artifact.rglob('*') if p.is_file()}
    if actual!=set(rows)|{'SHA256SUMS','archive-provenance.jsonl','oci-provenance.jsonl'}:
        raise ValueError('Unexpected/missing build assets')
    identity,manifest,config=inspect(artifact/'image.oci.tar')
    if (artifact/'image-manifest.json').read_bytes()!=manifest or (artifact/'image-config.json').read_bytes()!=config:
        raise ValueError('OCI metadata differs from the signed archive')
    if json.loads((artifact/'oci-identity.json').read_bytes())!=identity:
        raise ValueError('OCI identity mismatch')
    statements=[entry['verificationResult']['statement'] for entry in verifications['image-manifest.json']]
    if not any(s['name']=='ghcr.io/starknet-innovation/qsb-solver' and s['digest']=={'sha256':identity['imageDigest'][7:]}
               for statement in statements for s in statement['subject']):
        raise ValueError('OCI attestation has an unexpected subject')
    if (artifact/'source-commit').read_text().strip()!=COMMIT:raise ValueError('Build source differs')
    binding=json.loads((artifact/'binding.json').read_bytes())
    receipt=json.loads((artifact/'build-receipt.json').read_bytes())
    lock_raw=source(COMMIT,'research/pqb-ranked/source-lock.json');lock=json.loads(lock_raw)
    if binding['solverCommit']!=COMMIT or binding['status']!='HOLD' or binding['cudaArchitecture']!='86':
        raise ValueError('Installed binding differs')
    for name in ['pqb_handler.py','pqb_ranges.py']:
        if sha(source(COMMIT,'worker/pqb/'+name))!=binding['files'][name]:raise ValueError('Installed Python/source mismatch')
    if receipt['binarySha256']!=binding['files']['grind'] or receipt['sourceLock']!=lock or receipt['sourceLockSha256']!=sha(lock_raw):
        raise ValueError('Build receipt/source lock differs')
    if receipt['flags']!=['-O3','-std=c++17','-arch=sm_86','-I','/src/vendor/pqb/grinder']:
        raise ValueError('Compiler flags differ')
    for name,digest in lock['sources'].items():
        if sha(source(COMMIT,name))!=digest:raise ValueError('Actual source differs from lock')
    if sha(source(COMMIT,'vendor/pqb/'+lock['upstream']['adaptedFrom']))!=lock['upstream']['adaptedFromSha256']:
        raise ValueError('Upstream baseline differs')
    scan=json.loads((artifact/'image-scan/image-scan.json').read_bytes())
    if not scan['passed'] or scan['blocking']:raise ValueError('Image scan policy failed')
    contract=source(COMMIT,'contracts/pqb-ranked-v2.json')
    solver=dict(schemaVersion=3,id='pqb-ranked-v2-'+COMMIT[:12]+'-'+identity['imageDigest'][7:19],
        protocol='pqb-v1',generatorCommit=lock['upstream']['commit'],searchVersion='pqb-ranked-v2',
        searchContract=contract_hash(contract,source(COMMIT,'worker/pqb/pqb_ranges.py')),
        solverRepository='https://github.com/starknet-innovation/qsb-solver',solverCommit=COMMIT,kernelCommit=COMMIT,
        image='ghcr.io/starknet-innovation/qsb-solver@'+identity['imageDigest'])
    report=dict(format='qsb-pqb-verified-build-v1',status='passed',sourceCommit=COMMIT,sourceRef=REF,
        signerWorkflow=WORKFLOW,githubRunId=run_id,identity=identity,binding=binding,
        archiveSha256=rows['image.oci.tar'],buildAssetsSha256=file_sha(artifact/'SHA256SUMS'),
        verifiedSubjects=['signed archive','signed asset checksums','signed prospective OCI subject'],
        registryPublicationVerified=False,nativeQualification='pending',scanSummary=scan,
        limits=['Build provenance identifies source/artifact; it does not establish correctness or registry availability'])
    (out/'verified-build.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'descriptor-proposal.json').write_text(json.dumps(dict(format='qsb-pqb-final-descriptor-proposal-v1',
        status='HOLD',solver=solver,buildProvenanceVerified=True,imageReferenceStatus='prospective-unpublished',
        publicationVerified=False,enrollmentApproved=False,qualification='pending'),indent=2)+'\n')
    (out/'contract.json').write_bytes(contract)
    print(json.dumps(dict(status='passed',sourceCommit=COMMIT,imageDigest=identity['imageDigest'],binarySha256=binding['files']['grind'])))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('artifact',type=pathlib.Path);parser.add_argument('output',type=pathlib.Path)
    parser.add_argument('--source-commit',required=True);parser.add_argument('--source-ref',required=True)
    parser.add_argument('--run-id',type=int,required=True)
    args=parser.parse_args()
    verify(args.artifact,args.output,args.source_commit,args.source_ref,args.run_id)
