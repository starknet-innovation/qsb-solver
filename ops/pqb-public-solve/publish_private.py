"""Import a checked CI image into one temporary private ECR repository. No release enrollment."""
import argparse
import base64
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


def publish(artifact, repository, region, output):
    import boto3
    from botocore.config import Config
    artifact, output = Path(artifact), Path(output)
    if output.exists():
        raise ValueError('One-shot publisher receipt already exists')
    if not re.fullmatch(r'\d{12}\.dkr\.ecr\.eu-west-1\.amazonaws.com/qsb-pqb-solve-[a-z0-9-]+', repository):
        raise ValueError('Temporary private repository required')
    output.write_text('{"status":"started"}\n')
    checked = []
    for line in (artifact/'SHA256SUMS').read_text().splitlines():
        expected, name = line.split('  ', 1)
        if name not in ('image.tar.gz','image.json','binding.json','source-commit'):
            raise ValueError('Unexpected artifact entry')
        if hashlib.sha256((artifact/name).read_bytes()).hexdigest() != expected:
            raise ValueError('Artifact hash mismatch: '+name)
        checked.append(name)
    if sorted(checked) != sorted(('image.tar.gz','image.json','binding.json','source-commit')):
        raise ValueError('Incomplete or duplicate artifact checksum list')
    image = json.loads((artifact/'image.json').read_text())[0]
    binding = json.loads((artifact/'binding.json').read_text())
    commit = (artifact/'source-commit').read_text().strip()
    if binding['solverCommit'] != commit or binding['status'] != 'HOLD' or binding['cudaArchitecture'] != '86':
        raise ValueError('Artifact binding mismatch')
    subprocess.run(['docker','load','--input',str(artifact/'image.tar.gz')],check=True)
    actual = subprocess.check_output(['docker','inspect','--format','{{.Id}}','qsb-pqb:ci'],text=True).strip()
    if actual != image['Id']:
        raise ValueError('Loaded image identity mismatch')
    installed = json.loads(subprocess.check_output(['docker','run','--rm','--network','none','--read-only',
        '--entrypoint','cat','qsb-pqb:ci','/opt/qsb-pqb/binding.json'],text=True))
    if installed != binding:
        raise ValueError('Installed binding differs from CI artifact')
    client = boto3.client('ecr',region_name=region,config=Config(connect_timeout=5,read_timeout=30,
                          retries={'total_max_attempts':1}))
    account, name = repository.split('.dkr.ecr.',1)[0], repository.split('/',1)[1]
    target = repository+':validation-'+commit
    with tempfile.TemporaryDirectory(prefix='qsb-private-docker-') as temporary:
        env={**os.environ,'DOCKER_CONFIG':temporary}
        auth=client.get_authorization_token(registryIds=[account])['authorizationData'][0]
        user,password=base64.b64decode(auth['authorizationToken']).decode().split(':',1)
        subprocess.run(['docker','login','--username',user,'--password-stdin',repository.split('/')[0]],
                       input=password,text=True,env=env,check=True,capture_output=True)
        subprocess.run(['docker','tag','qsb-pqb:ci',target],env=env,check=True)
        subprocess.run(['docker','push',target],env=env,check=True)
    detail=client.describe_images(repositoryName=name,imageIds=[{'imageTag':'validation-'+commit}])['imageDetails'][0]
    digest=detail['imageDigest']
    manifest=client.batch_get_image(repositoryName=name,imageIds=[{'imageDigest':digest}])['images'][0]['imageManifest']
    if 'sha256:'+hashlib.sha256(manifest.encode()).hexdigest()!=digest:
        raise ValueError('Registry manifest digest mismatch')
    receipt={'status':'private-validation-only','sourceCommit':commit,'image':repository+'@'+digest,
             'imageId':actual,'binding':binding,'manifest':manifest}
    output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'image':receipt['image'],'sourceCommit':commit}),flush=True)


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('artifact');parser.add_argument('repository');parser.add_argument('region');parser.add_argument('output')
    args=parser.parse_args();publish(args.artifact,args.repository,args.region,args.output)
