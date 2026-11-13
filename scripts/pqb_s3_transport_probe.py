"""Public synthetic S3 round trip using the installed client's real HTTPS session.

Presigned URLs are mounted locally, never printed or retained in the public receipt.
This checks the changed TLS transport, not Batch dispatch or a native GPU invocation.
"""
import base64
import hashlib
import json
import os
from pathlib import Path
import sys
from unittest.mock import patch
from urllib.parse import urlsplit,unquote,parse_qs
import re


def validate_targets(spec):
    bucket,region,key=spec['bucket'],spec['region'],spec['key']
    if not re.fullmatch(r'[a-z0-9][a-z0-9.-]{1,61}[a-z0-9]',bucket) or not re.fullmatch(r'[a-z]{2}-[a-z]+-\d',region):
        raise ValueError('Invalid S3 target identity')
    if not key or key.startswith('/') or '\x00' in key:raise ValueError('Invalid S3 key')
    host=bucket+'.s3.'+region+'.amazonaws.com'
    for field in ('putUrl','getUrl'):
        url=urlsplit(spec[field]);query=parse_qs(url.query)
        if (url.scheme!='https' or url.netloc!=host or url.username is not None or url.fragment
                or unquote(url.path)!='/'+key):raise ValueError('S3 URL target differs')
        if query.get('X-Amz-Algorithm')!=['AWS4-HMAC-SHA256']:raise ValueError('Expected SigV4 S3 URL')
        credential=query.get('X-Amz-Credential',[])
        if len(credential)!=1 or credential[0].split('/')[2:]!=[region,'s3','aws4_request']:
            raise ValueError('S3 signing region/service differs')
        if not query.get('X-Amz-Signature'):raise ValueError('Unsigned S3 URL')
    return dict(bucket=bucket,region=region,key=key,host=host,validated=True)


def main():
    sys.path.insert(0,'/opt/qsb-pqb')
    import aws_entrypoint
    from botocore.awsrequest import AWSPreparedRequest
    spec=json.loads(Path(sys.argv[1]).read_bytes())
    target=validate_targets(spec)
    clients=[]
    with patch.object(aws_entrypoint,'run',lambda client,*args:clients.append(client)), \
         patch.dict(os.environ,{'AWS_EC2_METADATA_DISABLED':'true','AWS_DEFAULT_REGION':spec['region'],
                               'AWS_CA_BUNDLE':'/nonexistent/stale-bundle.pem'}):
        aws_entrypoint.main()
    if len(clients)!=1:raise ValueError('Expected one installed SDK client')
    client=clients[0];session=client._endpoint.http_session
    if session._verify!='/etc/ssl/certs/ca-certificates.crt':raise ValueError('Incorrect selected trust')
    binding=json.loads(Path('/opt/qsb-pqb/binding.json').read_bytes())
    if binding['solverCommit']!=spec['sourceCommit']:raise ValueError('Incorrect installed source')
    body=base64.b64decode(spec['bodyBase64'],validate=True)
    if hashlib.sha256(body).hexdigest()!=spec['bodySha256']:raise ValueError('Public payload differs')
    out=dict(format='qsb-installed-s3-transport-v1',status='failed',sourceCommit=binding['solverCommit'],
        scope=__doc__,caPath=session._verify,
        caSha256=hashlib.sha256(Path(session._verify).read_bytes()).hexdigest(),
        entrypointSha256=hashlib.sha256(Path(aws_entrypoint.__file__).read_bytes()).hexdigest(),
        config=dict(connectTimeout=client.meta.config.connect_timeout,readTimeout=client.meta.config.read_timeout,
                    retries=client.meta.config.retries),bodySha256=spec['bodySha256'],bodyBytes=len(body),
        key=spec['key'],target=target,requests=[],computeSubmitted=False,freshNativeExecution=False)
    try:
        for name,method,url,data,headers,want in (
            ('initial immutable PUT','PUT',spec['putUrl'],body,
             {'Content-Type':'application/json','If-None-Match':'*'},200),
            ('GET round trip','GET',spec['getUrl'],None,{},200),
            ('duplicate immutable PUT','PUT',spec['putUrl'],body,
             {'Content-Type':'application/json','If-None-Match':'*'},412)):
            response=session.send(AWSPreparedRequest(method=method,url=url,headers=headers,body=data,stream_output=False))
            row=dict(name=name,status=response.status_code,expectedStatus=want)
            if name=='GET round trip':row['receivedSha256']=hashlib.sha256(response.content).hexdigest()
            out['requests'].append(row)
            if response.status_code!=want or (name=='GET round trip' and response.content!=body):
                raise ValueError('S3 status/payload verification failed')
        out['status']='passed'
    except Exception as error:
        # Exception strings can contain the signed URL; retain only the type.
        out['errorType']=type(error).__name__
    finally:session.close()
    print(json.dumps(out,indent=2))
    return 0 if out['status']=='passed' else 1


if __name__=='__main__':raise SystemExit(main())
