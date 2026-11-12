"""One-shot publication of reviewed TLS replacement; copies an attested archive, never builds."""
import argparse,hashlib,json,os,pathlib,shutil,subprocess,sys
from verify_pqb_build import verify,verify_policy,WORKFLOW
from compare_pqb_runtime import assess
ROOT=pathlib.Path(__file__).resolve().parents[1]
REPO='starknet-innovation/qsb-solver'
NEW='cfd99e3844698f59679e4c15cf567db2976b9ffc';OLD='ecb31d384fbdec9c67cd802548460b774a722baf'
REF='refs/heads/codex/pqb-qualify-tls-20261112';OLDREF='refs/heads/codex/pqb-qualify-20261112'
RUN=43205074943;OLDRUN=43179921372
DIGEST='sha256:edce7a14b5548a079f8ebf1e866c533cb14573328cf739a6647b150cca08756e'
IMAGE='ghcr.io/'+REPO;TAG='pqb-aws-sm86-v0.1.0'
NATIVE='70526ef7da4920820e888bbaae5baa72b543e6b827ad1ea111f48584deb189ce'
APP='2bea83316fb66fb0fab0c30e7ae8206086059ffb'
EVIDENCE=ROOT/'docs/pqb/evidence/tls-replacement-2026-11-12'

def run(*args,**kw):return subprocess.run([str(x) for x in args],check=True,**kw)
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def capture(p,*args):
 r=run(*args,capture_output=True);p.write_bytes(r.stdout);return r.stdout

def main(work):
 work=work.resolve();work.mkdir(exist_ok=False);os.chdir(ROOT)
 decision=json.loads((EVIDENCE/'decision.json').read_bytes())
 if decision['releaseBlockers'] or decision['freshNativeExecution'] or decision['image']['imageDigest']!=DIGEST:raise ValueError('Unreviewed publication')
 manifest=json.loads((EVIDENCE/'manifest.json').read_bytes())
 for row in manifest['files']:
  p=EVIDENCE/row['path']
  if p.is_symlink() or p.stat().st_size!=row['bytes'] or sha(p)!=row['sha256']:raise ValueError('Evidence inventory differs')
 current=json.loads(capture(work/'main-before.json','gh','api','repos/'+REPO+'/commits/main'))
 if current['sha']!=NEW:raise ValueError('Main changed; review applicability before publication')
 for label,commit,ref,runid in [('reference',OLD,OLDREF,OLDRUN),('candidate',NEW,REF,RUN)]:
  artifact=work/label
  run('gh','run','download',str(runid),'--repo',REPO,'--name','pqb-qualified-sm86','--dir',artifact)
  verify(artifact,work/(label+'-verified'),commit,ref,runid)
  run('skopeo','copy','oci-archive:'+str(artifact/'image.oci.tar'),'docker-daemon:qsb-pqb:'+label)
 assess(work/'reference',work/'candidate','qsb-pqb:reference','qsb-pqb:candidate',work/'equivalence')
 capture(work/'offline-check.json','python3','worker/pqb/test_image.py','qsb-pqb:candidate')
 app=work/'app';run('git','clone','--no-checkout','https://github.com/starknet-innovation/qsb-app.git',app)
 run('git','-C',app,'checkout','--detach',APP);run('npm','ci','--ignore-scripts',cwd=app)
 old_evidence=ROOT/'docs/pqb/evidence/final-image-2026-11-12'
 run('python3','scripts/check_pqb_final.py',app,APP,old_evidence/'native/public-result.json.gz',NATIVE,
     work/'reference-verified/descriptor-proposal.json',work/'original-native-consumer',
     '--build-artifacts',work/'reference','--native-gate-checksums',old_evidence/'verification/native-gate-SHA256SUMS',
     '--native-gate-commit','4dff68d2eeeeaed7b437eb598f668d33a7f47205')
 capture(work/'installed-wrapper-replay.json','docker','run','--rm','--network','none','--read-only','--tmpfs','/tmp:rw,size=256m',
     '--mount','type=bind,src='+str(old_evidence/'native/public-result.json.gz')+',dst=/original-native.json.gz,readonly',
     '--mount','type=bind,src='+str(ROOT/'research/pqb-ranked/tests/fixtures')+',dst=/public-fixtures,readonly',
     '--mount','type=bind,src='+str(ROOT/'scripts/replay_pqb_installed_wrapper.py')+',dst=/replay.py,readonly',
     '--entrypoint','python3','qsb-pqb:candidate','/replay.py','/original-native.json.gz',NATIVE,NEW)
 run('python3','scripts/check_pqb_wrapper_consumer.py',app,APP,work/'installed-wrapper-replay.json',
     work/'candidate-verified/descriptor-proposal.json',work/'wrapper-consumer')
 run('python3','scripts/image_scan.py','oci-archive:'+str(work/'candidate/image.oci.tar'),work/'fresh-scan')
 scan=json.loads((work/'fresh-scan/image-scan.json').read_bytes());reviewed=json.loads((EVIDENCE/'build/image-scan/image-scan.json').read_bytes())
 if not scan['passed'] or scan['blocking'] or sorted(scan['unfixedCritical'],key=lambda f:(f['id'],f['package']))!=sorted(reviewed['unfixedCritical'],key=lambda f:(f['id'],f['package'])):raise ValueError('Critical inventory changed; new review required')
 release=work/'release';release.mkdir()
 for src in (work/'candidate').rglob('*'):
  if src.is_file() and src.name!='image.oci.tar':
   dst=release/'build'/src.relative_to(work/'candidate');dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
 solver=json.loads((work/'candidate-verified/descriptor-proposal.json').read_bytes())['solver'];save(release/'solver.json',solver)
 shutil.copyfile(work/'candidate-verified/contract.json',release/'pqb-ranked-v2.json')
 for folder in ['candidate-verified','reference-verified','equivalence','original-native-consumer','wrapper-consumer','fresh-scan']:
  shutil.copytree(work/folder,release/folder)
 shutil.copytree(EVIDENCE,release/'reviewed-evidence')
 for name in ['offline-check.json','installed-wrapper-replay.json']:shutil.copyfile(work/name,release/name)
 # Publication is conditional on all preceding independent checks; no old image is pushed.
 run('skopeo','copy','--all','--preserve-digests','oci-archive:'+str(work/'candidate/image.oci.tar'),'docker://'+IMAGE+':'+TAG)
 actual=capture(release/'registry-index.json','skopeo','inspect','--raw','docker://'+IMAGE+'@'+DIGEST)
 if actual!=(work/'candidate/image-manifest.json').read_bytes():raise ValueError('Registry index differs')
 identity=json.loads((work/'candidate/oci-identity.json').read_bytes())
 platform=capture(release/'registry-platform.json','skopeo','inspect','--raw','docker://'+IMAGE+'@'+identity['platformDigest'])
 if 'sha256:'+hashlib.sha256(platform).hexdigest()!=identity['platformDigest'] or json.loads(platform)['config']['digest']!=identity['configDigest']:raise ValueError('Registry platform differs')
 config=capture(release/'registry-config.json','skopeo','inspect','--config','--raw','docker://'+IMAGE+'@'+identity['platformDigest'])
 if 'sha256:'+hashlib.sha256(config).hexdigest()!=identity['configDigest']:raise ValueError('Registry config differs')
 # Attach the ORIGINAL signed build bundle, preserving the real builder/source/run.
 run('oras','attach','--artifact-type','application/vnd.dev.sigstore.bundle.v0.3+json',IMAGE+'@'+DIGEST,
     'oci-provenance.jsonl:application/vnd.dev.sigstore.bundle.v0.3+json',cwd=work/'candidate')
 policy=['--repo',REPO,'--signer-workflow',WORKFLOW,'--source-ref',REF,'--source-digest',NEW,'--deny-self-hosted-runners','--format','json']
 for label,extra in [('registry',['--bundle-from-oci']),('github-api',[])]:
  raw=capture(release/('oci-'+label+'-verification.json'),'gh','attestation','verify','oci://'+IMAGE+'@'+DIGEST,*extra,*policy)
  verify_policy(json.loads(raw),NEW,REF,RUN)
 # Retain the approved archive beyond Actions expiry, split below the per-file release limit.
 run('split','--bytes=1500000000','--numeric-suffixes=1','--suffix-length=2',work/'candidate/image.oci.tar',release/'image.oci.tar.part-')
 save(release/'archive-parts.json',dict(archiveSha256=sha(work/'candidate/image.oci.tar'),parts=[dict(file=p.name,bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(release.glob('image.oci.tar.part-*'))]))
 save(release/'publication.json',dict(format='qsb-pqb-tls-publication-v1',status='verified',sourceCommit=NEW,image=IMAGE+'@'+DIGEST,
   identity=identity,originalBuildRun=RUN,buildSourceRef=REF,publicationCommit=os.environ['GITHUB_SHA'],publicationRun=os.environ['GITHUB_RUN_ID'],
   qualification=decision['qualification'],freshNativeExecution=False,newPerformanceClaim=False,originalNativeArchiveSha256=NATIVE,
   releaseBlockers=[],registryDigestVerified=True,originalRegistryBuildProvenanceVerified=True,enrolled=False,deployed=False))
 # Package metadata/evidence under stable paths, rather than flattening duplicate basenames.
 run('tar','-czf',work/'qualification-evidence.tar.gz','--exclude=image.oci.tar.part-*','-C',release,'.')
 notes=work/'release-notes.md'
 notes.write_text('TLS-fixed PQB worker from merged main `'+NEW+'`.\n\nImage: `'+IMAGE+'@'+DIGEST+'`.\n\nQualification uses retained A10G native compute evidence with complete runtime applicability proof, plus fresh installed TLS and real S3 transport checks. **No new GPU execution or performance measurement.** The original native archive keeps its old source/image identity. All 20 unfixed Critical scanner matches remain disclosed; four are mitigated on the supported S3 path and the other exploit preconditions are outside the supported workload.\n\nThe archive is copied without rebuilding. Original build provenance verifies both from the registry and GitHub API. See `publication.json`, `qualification-evidence.tar.gz`, signed build assets and source notices. Reassemble the two archive parts in numeric order and check `archive-parts.json` and the original signed `SHA256SUMS`.\n\nDescriptor enrollment and deployment are separate. No default, serving infrastructure, mainnet switch, wallet or transaction is changed. First PQB release: stop/drain PQB work before removing enrollment; the historical QSB worker cannot resume PQB. Consumer statistical gate policy still needs separate review before serving.\n')
 assets=[release/x for x in ['solver.json','pqb-ranked-v2.json','publication.json','archive-parts.json']]
 assets += sorted(release.glob('image.oci.tar.part-*'))+[work/'qualification-evidence.tar.gz']
 run('gh','release','create',TAG,'--repo',REPO,'--target',NEW,'--prerelease','--title','PQB sm86 TLS-fixed worker v0.1.0','--notes-file',notes,*assets)
 print(json.dumps(dict(status='published-and-provenance-verified',image=IMAGE+'@'+DIGEST,tag=TAG,freshNativeExecution=False)))

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('work',type=pathlib.Path);main(p.parse_args().work)
