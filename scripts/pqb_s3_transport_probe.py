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


def main():
    sys.path.insert(0,'/opt/qsb-pqb')
    import aws_entrypoint
    from botocore.awsrequest import AWSPreparedRequest
    spec=json.loads(Path(sys.argv[1]).read_bytes())
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
        key=spec['key'],requests=[],computeSubmitted=False,freshNativeExecution=False)
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
