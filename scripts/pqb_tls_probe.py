"""Check the installed S3 client's trust with public TLS handshakes only.

Run inside the assessed image with public certificate fixtures mounted read-only.
No credentials, HTTP requests, AWS API calls or certificate-verification bypass.
"""
import concurrent.futures
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import ssl
import sys
import time
from unittest.mock import patch


def main():
    import aws_entrypoint
    from botocore.httpsession import create_urllib3_context
    fixtures=Path(sys.argv[1])
    expected_source=sys.argv[2]
    binding=json.loads(Path('/opt/qsb-pqb/binding.json').read_bytes())
    if binding['solverCommit']!=expected_source:
        raise ValueError('Installed source differs from assessed image')
    clients=[]
    with patch.object(aws_entrypoint,'run',lambda client,*args:clients.append(client)), \
         patch.dict(os.environ,{'AWS_EC2_METADATA_DISABLED':'true','AWS_DEFAULT_REGION':'eu-west-1',
                               'AWS_CA_BUNDLE':'/nonexistent/stale-bundle.pem'}):
        aws_entrypoint.main()
    if len(clients)!=1:
        raise ValueError('Expected one real installed SDK client')
    ca=clients[0]._endpoint.http_session._verify
    if ca!='/etc/ssl/certs/ca-certificates.crt':
        raise ValueError('Unexpected installed transport trust selection')
    inventory=json.loads((fixtures/'provenance.json').read_bytes())
    hosts=[('www.python.org',None),('s3.eu-west-1.amazonaws.com',None)]
    for row in inventory['chains']:
        pem=(fixtures/row['path']).read_bytes()
        if hashlib.sha256(pem).hexdigest()!=row['sha256']:
            raise ValueError('Public certificate fixture hash differs')
        if row['path'].startswith('regular/'):
            leaf=re.search(r'-----BEGIN CERTIFICATE-----.*?-----END CERTIFICATE-----',pem.decode(),re.S)[0]
            hosts.append((Path(row['path']).stem,hashlib.sha256(ssl.PEM_cert_to_DER_cert(leaf)).hexdigest()))
    if len(hosts)!=16:
        raise ValueError('Expected 14 bad hosts and two valid controls')
    def check(row):
        host,expected=row
        context=create_urllib3_context()
        context.load_verify_locations(cafile=ca)
        context.check_hostname=True
        started=time.monotonic()
        out=dict(host=host,expectedLeafSha256=expected)
        try:
            with socket.create_connection((host,443),timeout=8) as raw:
                with context.wrap_socket(raw,server_hostname=host) as tls:
                    digest=hashlib.sha256(tls.getpeercert(binary_form=True)).hexdigest()
                    out.update(status='accepted',leafSha256=digest,protocol=tls.version())
        except ssl.SSLCertVerificationError as error:
            out.update(status='certificate-rejected',verifyCode=error.verify_code,verifyMessage=error.verify_message)
        except (OSError,ssl.SSLError) as error:
            out.update(status='inconclusive',error=type(error).__name__+': '+str(error))
        out['seconds']=time.monotonic()-started
        return out
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results=list(pool.map(check,hosts))
    passed=all(r['status']=='accepted' if r['expectedLeafSha256'] is None else
               r['status']=='certificate-rejected' and r['verifyCode'] in (20,21) for r in results)
    print(json.dumps(dict(format='qsb-installed-s3-tls-v1',status='passed' if passed else 'failed',
        scope=__doc__,sourceCommit=expected_source,binding=binding,python=sys.version,
        entrypointSha256=hashlib.sha256(Path(aws_entrypoint.__file__).read_bytes()).hexdigest(),
        caPath=ca,caSha256=hashlib.sha256(Path(ca).read_bytes()).hexdigest(),results=results),indent=2))
    return 0 if passed else 1


if __name__=='__main__':
    raise SystemExit(main())
