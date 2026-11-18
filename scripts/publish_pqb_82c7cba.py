"""Publish the reviewed sm86 artifact from its original signed archive."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from publish_pqb_tls import REPO, IMAGE, ROOT, verify_archive_parts
from verify_pqb_build import verify, verify_policy, WORKFLOW

SOURCE = '80d306ec74b0c5f5a8bd95a2c94ab047bafd2a28'
SOURCE_REF = 'refs/heads/codex/pqb-qualify-82c7cba'
BUILD = 44280016361
TAG = 'pqb-aws-sm86-v0.2.0'
INDEX = 'sha256:bcc69b5d33ac7ddbabd5a8822081acef275c02cf0232f93bd04fab0865a16f78'
EVIDENCE = ROOT / 'docs/pqb/evidence/adoption-2026-11-18/virginia'


def run(*args, cwd=None):
    return subprocess.check_output(args, cwd=cwd)


def digest(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main(work):
    work.mkdir()
    os.chdir(ROOT)
    release = work / 'assets'
    release.mkdir()
    metadata = work / 'metadata'
    metadata.mkdir()
    artifact = metadata / 'build'
    verified = metadata / 'verified'
    run('gh','run','download',str(BUILD),'--repo',REPO,'--name','pqb-qualified-sm86','--dir',artifact)
    verify(artifact, verified, SOURCE, SOURCE_REF, BUILD)
    signed = json.loads((verified/'verified-build.json').read_bytes())
    identity = signed['identity']
    assert identity['imageDigest'] == INDEX
    proposal = json.loads((verified/'descriptor-proposal.json').read_bytes())
    assert proposal == json.loads((EVIDENCE/'build-time-proposal.json').read_bytes())
    for name, expected in json.loads((EVIDENCE/'campaign.json').read_bytes())['receiptHashes'].items():
        assert digest(EVIDENCE/name) == expected
    consumer = json.loads((EVIDENCE/'release-review-consumer.json').read_bytes())
    assert consumer['status'] == 'passed' and consumer['archiveSha256'] == digest(EVIDENCE/'native.json.gz')
    archive = artifact/'image.oci.tar'
    local = 'qsb-pqb:reviewed'
    run('skopeo','copy','oci-archive:'+str(archive),'docker-daemon:'+local)
    (metadata/'installed-check.json').write_bytes(run('python3','worker/pqb/test_image.py',local))
    run('python3','scripts/image_scan.py','oci-archive:'+str(archive), metadata/'fresh-scan')
    scan = json.loads((metadata/'fresh-scan/image-scan.json').read_bytes())
    order = lambda r: (r['id'], r['package'])
    assert scan['passed'] and not scan['blocking']
    assert sorted(scan['unfixedCritical'],key=order) == sorted(signed['scanSummary']['unfixedCritical'],key=order)
    run('docker','image','rm',local)
    save(release/'solver.json', proposal['solver'])
    shutil.copy(verified/'contract.json',release/'pqb-ranked-v2.json')
    shutil.copytree(EVIDENCE,metadata/'native')
    target = IMAGE + '@' + INDEX
    # Preflight both tag namespaces. Fail closed on authentication or network errors.
    tag = subprocess.run(['gh','api','repos/'+REPO+'/git/ref/tags/'+TAG],capture_output=True)
    if tag.returncode == 0 or b'HTTP 404' not in tag.stderr:
        raise RuntimeError('Could not confirm a new Git release tag')
    image_tag = subprocess.run(['skopeo','inspect','--raw','docker://'+IMAGE+':'+TAG],capture_output=True)
    if image_tag.returncode == 0 or b'manifest unknown' not in image_tag.stderr.lower():
        raise RuntimeError('Could not confirm a new image tag: '+image_tag.stderr.decode())
    assert run('gh','api','repos/'+REPO+'/git/ref/heads/codex/pqb-publish-82c7cba','--jq','.object.sha').decode().strip()==os.environ['GITHUB_SHA']
    run('skopeo','copy','--all','--preserve-digests','oci-archive:'+str(archive),'docker://'+IMAGE+':pqb-staging-'+os.environ['GITHUB_RUN_ID'])
    for label, ref, flags, expected in [
        ('index',INDEX,[],INDEX),
        ('platform',identity['platformDigest'],[],identity['platformDigest']),
        ('config',identity['platformDigest'],['--config'],identity['configDigest'])]:
        raw = run('skopeo','inspect',*flags,'--raw','docker://'+IMAGE+'@'+ref)
        assert 'sha256:'+hashlib.sha256(raw).hexdigest()==expected
        (metadata/(label+'.json')).write_bytes(raw)
    run('oras','attach','--artifact-type','application/vnd.dev.sigstore.bundle.v0.3+json',target,
        'oci-provenance.jsonl:application/vnd.dev.sigstore.bundle.v0.3+json',cwd=artifact)
    for label, flags in [('registry',['--bundle-from-oci']),('github',[])]:
        raw = run('gh','attestation','verify','oci://'+target,*flags,'--repo',REPO,'--signer-workflow',WORKFLOW,
                  '--source-ref',SOURCE_REF,'--source-digest',SOURCE,'--deny-self-hosted-runners','--format','json')
        verify_policy(json.loads(raw),SOURCE,SOURCE_REF,BUILD)
        (metadata/(label+'-provenance.json')).write_bytes(raw)
    run('split','--bytes=1500000000','--numeric-suffixes=1','--suffix-length=2',archive,release/'image.oci.tar.part-')
    parts = dict(archiveSha256=signed['archiveSha256'],parts=[
        dict(file=p.name,bytes=p.stat().st_size,sha256=digest(p)) for p in sorted(release.glob('image.oci.tar.part-*'))])
    verify_archive_parts(release,parts,signed['archiveSha256'])
    save(release/'archive-parts.json',parts)
    save(release/'publication.json',dict(image=target,sourceCommit=SOURCE,originalBuildRun=BUILD,identity=identity,
        nativeArchiveSha256=consumer['archiveSha256'],scanBlocking=0,unfixedCritical=len(scan['unfixedCritical']),
        controllerCommit=os.environ['GITHUB_SHA'],registryAndGithubProvenanceVerified=True))
    run('tar','-czf',release/'qualification-evidence.tar.gz','--exclude=./build/image.oci.tar','-C',metadata,'.')
    notes=work/'notes.md'
    notes.write_text('PQB CUDA sm86 worker based on Fireblocks 82c7cba. The signed archive from build 44280016361 was copied by digest. '
        'Three full native A10G ranges and the independent consumer replay passed. Three paired samples per stage showed essentially flat pinning and round 0, and about 1.2% faster round 1. '
        'Full-solve performance remains unmeasured. The scan reports ten unfixed Critical package matches. The installed S3 client passed the compromised-chain regressions. '
        'The supported worker has no Python TLS or SASL SRP server. The prior release remains available for rollback.\n\n'+target+'\n')
    run('gh','release','create',TAG,'--repo',REPO,'--target',SOURCE,'--prerelease','--title','PQB sm86 worker v0.2.0',
        '--notes-file',notes,*sorted(release.iterdir()))
    assert run('gh','api','repos/'+REPO+'/git/ref/tags/'+TAG,'--jq','.object.sha').decode().strip()==SOURCE
    run('skopeo','copy','--all','--preserve-digests','docker://'+target,'docker://'+IMAGE+':'+TAG)
    assert run('skopeo','inspect','--raw','docker://'+IMAGE+':'+TAG)==(metadata/'index.json').read_bytes()


if __name__=='__main__':
    main(Path(sys.argv[1]).resolve())
