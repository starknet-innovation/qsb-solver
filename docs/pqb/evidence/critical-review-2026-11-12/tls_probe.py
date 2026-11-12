"""Credential-free TLS handshakes to the disclosure's public test hosts; no HTTP/AWS calls."""
import concurrent.futures,hashlib,json,pathlib,re,socket,ssl,sys,time
from botocore.httpsession import create_urllib3_context,get_cert_path
ca=get_cert_path(True)
paths=sorted(pathlib.Path('/probe/chains/chains/regular').glob('*.pem'))
def check(row):
 host,expected=row;ctx=create_urllib3_context();ctx.load_verify_locations(cafile=ca);ctx.check_hostname=True
 start=time.monotonic();out={'host':host,'expectedLeafSha256':expected}
 try:
  with socket.create_connection((host,443),timeout=8) as raw:
   with ctx.wrap_socket(raw,server_hostname=host) as tls:
    digest=hashlib.sha256(tls.getpeercert(binary_form=True)).hexdigest()
    out.update(status='accepted',leafSha256=digest,leafMatchesPublishedChain=(digest==expected if expected else None),protocol=tls.version())
 except ssl.SSLCertVerificationError as e:out.update(status='certificate-rejected',verifyCode=e.verify_code,verifyMessage=e.verify_message)
 except Exception as e:out.update(status='inconclusive',error=type(e).__name__+': '+str(e))
 out['seconds']=time.monotonic()-start;return out
rows=[('www.python.org',None)]
for p in paths:
 leaf=re.search(r'-----BEGIN CERTIFICATE-----.*?-----END CERTIFICATE-----',p.read_text(),re.S)[0]
 rows.append((p.name.removesuffix('.pem'),hashlib.sha256(ssl.PEM_cert_to_DER_cert(leaf)).hexdigest()))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:results=list(pool.map(check,rows))
print(json.dumps({'scope':__doc__,'caPath':ca,'caSha256':hashlib.sha256(pathlib.Path(ca).read_bytes()).hexdigest(),'python':sys.version,'results':results},indent=2))
