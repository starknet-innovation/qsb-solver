"""Compare independently attestation-verified archives with the retained native stack.

Containers are only created/exported, never started. This is component applicability
evidence, not a new GPU execution or timing attestation. Verify both build artifacts
with verify_pqb_build.py and import their exact archives before calling this program.
"""
import argparse
import ast
import copy
import gzip
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import tarfile
import uuid
from pqb_descriptor import source, sha
from pqb_import import verify_runtime

INSTALLATION_DATA = {'var/cache/ldconfig/aux-cache','var/log/alternatives.log',
                     'var/log/apt/history.log','var/log/apt/term.log','var/log/dpkg.log'}
SEMANTIC_FILES = {'opt/qsb-pqb/aws_entrypoint.py','opt/qsb-pqb/binding.json',
                  'opt/qsb-pqb/licenses/LICENSES.md'}


def ca_only_delta(before,after):
    old,new=ast.parse(before),ast.parse(after)
    calls=[node for node in ast.walk(new) if isinstance(node,ast.Call)
           and isinstance(node.func,ast.Attribute) and node.func.attr=='client'
           and isinstance(node.func.value,ast.Name) and node.func.value.id=='boto3'
           and node.args and isinstance(node.args[0],ast.Constant) and node.args[0].value=='s3']
    if len(calls)!=1:raise ValueError('Expected one S3 client constructor')
    keywords=[k for k in calls[0].keywords if k.arg=='verify']
    if len(keywords)!=1 or not isinstance(keywords[0].value,ast.Constant) \
            or keywords[0].value.value!='/etc/ssl/certs/ca-certificates.crt':
        raise ValueError('Transport patch is not the reviewed CA selection')
    calls[0].keywords.remove(keywords[0])
    if ast.dump(old,include_attributes=False)!=ast.dump(new,include_attributes=False):
        raise ValueError('Transport has another semantic change')


def pyc_timestamp_only(path,before,after,old,new):
    p=PurePosixPath(path)
    if p.parent.name!='__pycache__' or '.cpython-' not in p.name:return False
    src=str(p.parent.parent/(p.name.split('.cpython-')[0]+'.py'))
    if src not in old or src not in new:return False
    a,b=old[src],new[src]
    x,y=bytes.fromhex(before['pycHeader']),bytes.fromhex(after['pycHeader'])
    return (len(x)==len(y)==16 and x[:8]==y[:8] and int.from_bytes(x[4:8],'little')==0
        and x[12:16]==y[12:16] and before['pycCodeSha256']==after['pycCodeSha256']
        and a['sha256']==b['sha256'] and a['type']==b['type']=='0'
        and int.from_bytes(x[8:12],'little')==int(a['mtime'])
        and int.from_bytes(y[8:12],'little')==int(b['mtime'])
        and int.from_bytes(x[12:16],'little')==a['size']==b['size'])


def compare_tables(old,new):
    if set(old)!=set(new):raise ValueError('Filesystem inventory changed')
    changes=[];timestamps=[];pycs=[]
    for path in sorted(old):
        a,b=old[path],new[path]
        if a==b:continue
        for key in ('type','mode','uid','gid','link'):
            if a[key]!=b[key]:raise ValueError('Filesystem semantics changed: '+path)
        if {k:v for k,v in a.items() if k!='mtime'}=={k:v for k,v in b.items() if k!='mtime'}:
            timestamps.append(path);continue
        if path.endswith('.pyc'):
            if a['size']!=b['size'] or not pyc_timestamp_only(path,a,b,old,new):
                raise ValueError('Python code/cache semantics changed: '+path)
            pycs.append(path)
        elif path in INSTALLATION_DATA:
            if a['type']!='0' or a['size']!=b['size'] or a['mode']&0o111:
                raise ValueError('Unexpected installation data shape: '+path)
        elif path not in SEMANTIC_FILES:
            raise ValueError('Unreviewed file content changed: '+path)
        changes.append(dict(path=path,oldSha256=a.get('sha256'),newSha256=b.get('sha256')))
    if set(c['path'] for c in changes if not c['path'].endswith('.pyc'))!=INSTALLATION_DATA|SEMANTIC_FILES:
        raise ValueError('Expected exact reviewed TLS/binding/notices/install-data delta')
    return dict(files=len(old),changes=changes,timestampOnlyPaths=timestamps,pythonCacheTimestampPaths=pycs)


def inventory(label,image,artifact,out):
    identity=json.loads((artifact/'oci-identity.json').read_bytes())
    config_raw=(artifact/'image-config.json').read_bytes()
    if 'sha256:'+sha(config_raw)!=identity['configDigest']:raise ValueError('Artifact config identity differs')
    inspected=json.loads(subprocess.check_output(['docker','image','inspect',image]))[0]
    verify_runtime(inspected,json.loads(config_raw))
    (out/(label+'-image.json')).write_text(json.dumps(inspected,indent=2)+'\n')
    container=subprocess.check_output(['docker','create','--platform','linux/amd64','--network','none','--read-only',
        '--name','qsb-runtime-'+label+'-'+uuid.uuid4().hex[:8],'--entrypoint','true',inspected['Id']],text=True).strip()
    (out/(label+'-container.txt')).write_text(container+'\n')
    rows={}
    try:
        process=subprocess.Popen(['docker','export',container],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        with tarfile.open(fileobj=process.stdout,mode='r|') as archive:
            for member in archive:
                name=member.name.removeprefix('./').rstrip('/')
                if not name:continue
                if name in rows or name.startswith('/') or '..' in PurePosixPath(name).parts:
                    raise ValueError('Unsafe or duplicate export path')
                row=dict(type=member.type.decode(),mode=member.mode,uid=member.uid,gid=member.gid,
                         size=member.size,link=member.linkname,mtime=member.mtime)
                if member.isfile():
                    digest=hashlib.sha256();code=hashlib.sha256();header=b''
                    stream=archive.extractfile(member)
                    for chunk in iter(lambda:stream.read(1024*1024),b''):
                        digest.update(chunk)
                        if name.endswith('.pyc'):
                            needed=16-len(header);header+=chunk[:needed];code.update(chunk[needed:])
                    row['sha256']=digest.hexdigest()
                    if name.endswith('.pyc'):row.update(pycHeader=header.hex(),pycCodeSha256=code.hexdigest())
                rows[name]=row
        process.stdout.close();error=process.stderr.read().decode();status=process.wait()
        if status:raise RuntimeError(error)
    finally:subprocess.run(['docker','rm','--force',container],check=True,capture_output=True)
    (out/(label+'-files.json.gz')).write_bytes(gzip.compress(json.dumps(rows,sort_keys=True).encode(),mtime=0))
    return inspected,rows


def assess(old_artifact,new_artifact,old_image,new_image,out):
    if any(out.resolve().is_relative_to(p.resolve()) for p in
           (Path(__file__).resolve().parents[1],old_artifact,new_artifact)):
        raise ValueError('Keep working inventories outside source and artifact directories')
    out.mkdir(exist_ok=False)
    old_inspect,old=inventory('old',old_image,old_artifact,out)
    new_inspect,new=inventory('new',new_image,new_artifact,out)
    if old_inspect['Config']!=new_inspect['Config']:raise ValueError('Runtime configuration changed')
    result=compare_tables(old,new)
    bindings=[json.loads((p/'binding.json').read_bytes()) for p in (old_artifact,new_artifact)]
    for binding,files,artifact in zip(bindings,(old,new),(old_artifact,new_artifact)):
        if files['opt/qsb-pqb/binding.json']['sha256']!=sha((artifact/'binding.json').read_bytes()):
            raise ValueError('Actual image binding differs from verified artifact')
        for name,digest in binding['files'].items():
            if files['opt/qsb-pqb/'+name]['sha256']!=digest:raise ValueError('Installed compute file differs')
        for path,git_path in [('opt/qsb-pqb/aws_entrypoint.py','worker/aws/entrypoint.py'),
                              ('opt/qsb-pqb/licenses/LICENSES.md','LICENSES.md')]:
            if files[path]['sha256']!=sha(source(binding['solverCommit'],git_path)):
                raise ValueError('Actual transport/notice differs from committed source')
    stripped=copy.deepcopy(bindings)
    for b in stripped:del b['solverCommit']
    if stripped[0]!=stripped[1]:raise ValueError('Compute binding changed beyond source identity')
    if (old_artifact/'build-receipt.json').read_bytes()!=(new_artifact/'build-receipt.json').read_bytes():
        raise ValueError('Compiler/binary receipt changed')
    if (old_artifact/'packages.txt').read_bytes()!=(new_artifact/'packages.txt').read_bytes():
        raise ValueError('Installed package versions changed')
    ca_only_delta(source(bindings[0]['solverCommit'],'worker/aws/entrypoint.py'),
                  source(bindings[1]['solverCommit'],'worker/aws/entrypoint.py'))
    result.update(format='qsb-pqb-compute-applicability-v1',status='passed',
        oldImage=json.loads((old_artifact/'oci-identity.json').read_bytes()),
        newImage=json.loads((new_artifact/'oci-identity.json').read_bytes()),
        referenceSourceCommit=bindings[0]['solverCommit'],assessedSourceCommit=bindings[1]['solverCommit'],
        computeFiles=bindings[1]['files'],runtimeConfigurationEqual=True,compilerReceiptEqual=True,packagesEqual=True,
        transportSemanticDelta='Only explicit S3 verify=/etc/ssl/certs/ca-certificates.crt',
        harnessSha256=sha(Path(__file__).read_bytes()),
        freshNativeExecution=False,
        limits=['Retained native compute evidence applies to identical components; not a new GPU run or timing',
                'File mtimes and validated timestamp-only Python cache headers differ',
                'Installation logs and ldconfig auxiliary index differ; runtime loader cache and libraries are identical',
                'No new complete solve, served coordinator, wallet, consensus, miner or broadcast evidence'])
    (out/'applicability.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(dict(status='passed',files=result['files'],changed=len(result['changes']),
        pycTimestampChanges=len(result['pythonCacheTimestampPaths']),freshNativeExecution=False)))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('old_artifact',type=Path);parser.add_argument('new_artifact',type=Path)
    parser.add_argument('old_image');parser.add_argument('new_image');parser.add_argument('output',type=Path)
    a=parser.parse_args();assess(a.old_artifact,a.new_artifact,a.old_image,a.new_image,a.output)
