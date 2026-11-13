"""Check the installed S3 client's trust with public TLS handshakes only.

Run inside the assessed image with public certificate fixtures mounted read-only.
No credentials, HTTP requests or AWS API calls. Independent unverified handshakes
observe public leaf bytes only; the installed-client trust check always verifies.
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


def observe_leaf(host):
    # Observe public bytes only. Never use this context for HTTP, credentials or SDK calls.
    context=ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.check_hostname=False
    context.verify_mode=ssl.CERT_NONE
    with socket.create_connection((host,443),timeout=8) as raw:
        with context.wrap_socket(raw,server_hostname=host) as tls:
            return hashlib.sha256(tls.getpeercert(binary_form=True)).hexdigest()


def accepted_evidence(row):
    if row['expectedLeafSha256'] is None:return row['status']=='accepted'
    return (row['status']=='certificate-rejected' and row['verifyCode'] in (20,21)
        and row.get('observedLeafBeforeSha256')==row['expectedLeafSha256']
        and row.get('observedLeafAfterSha256')==row['expectedLeafSha256'])


def main():
    sys.path.insert(0,'/opt/qsb-pqb')
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
            if expected is not None:
                out['observedLeafBeforeSha256']=observe_leaf(host)
                if out['observedLeafBeforeSha256']!=expected:
                    out['status']='leaf-mismatch'
                    return out
            with socket.create_connection((host,443),timeout=8) as raw:
                with context.wrap_socket(raw,server_hostname=host) as tls:
                    digest=hashlib.sha256(tls.getpeercert(binary_form=True)).hexdigest()
                    out.update(status='accepted',leafSha256=digest,protocol=tls.version())
        except ssl.SSLCertVerificationError as error:
            out.update(status='certificate-rejected',verifyCode=error.verify_code,verifyMessage=error.verify_message)
        except (OSError,ssl.SSLError) as error:
            out.update(status='inconclusive',error=type(error).__name__+': '+str(error))
        if expected is not None and out['status']=='certificate-rejected':
            try:out['observedLeafAfterSha256']=observe_leaf(host)
            except (OSError,ssl.SSLError) as error:
                out.update(status='inconclusive',error=type(error).__name__)
        out['seconds']=time.monotonic()-started
        return out
    with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
        results=list(pool.map(check,hosts))
    passed=all(accepted_evidence(r) for r in results)
    print(json.dumps(dict(format='qsb-installed-s3-tls-v1',status='passed' if passed else 'failed',
        scope=__doc__,sourceCommit=expected_source,binding=binding,python=sys.version,
        entrypointSha256=hashlib.sha256(Path(aws_entrypoint.__file__).read_bytes()).hexdigest(),
        caPath=ca,caSha256=hashlib.sha256(Path(ca).read_bytes()).hexdigest(),results=results),indent=2))
    return 0 if passed else 1


if __name__=='__main__':
    raise SystemExit(main())
