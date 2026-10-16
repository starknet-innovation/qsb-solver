"""Host-only snapshot/intent ACK supervisor. No provisioning or automatic retries.

The presigned upload capability remains on the host, never inside the container.
One container invocation performs at most one range. Upload failure stops work.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time
import urllib.request

MAX_BYTES=256*1024*1024

def snapshot(root, destination):
    files=sorted(p for p in root.rglob('*') if p.is_file())
    if any(p.is_symlink() for p in root.rglob('*')):
        raise ValueError('Snapshot symlink forbidden')
    if sum(p.stat().st_size for p in files)>MAX_BYTES:
        raise ValueError('Snapshot size exceeded')
    with tarfile.open(destination,'w:gz') as archive:
        for path in files:
            archive.add(path,arcname=str(path.relative_to(root)),recursive=False)
    if destination.stat().st_size>MAX_BYTES:
        raise ValueError('Compressed snapshot size exceeded')

def upload(root,url):
    if not url.startswith('https://'):
        raise ValueError('HTTPS upload required')
    with tempfile.TemporaryDirectory(prefix='qsb-checkpoint-') as tmp:
        path=Path(tmp)/'checkpoint.tar.gz'
        snapshot(root,path)
        data=path.read_bytes()
        # PUT to the same object is idempotent, but this supervisor deliberately
        # stops on uncertain upload rather than dispatching additional work.
        request=urllib.request.Request(url,data=data,method='PUT')
        try:
            with urllib.request.urlopen(request,timeout=60) as response:
                if response.status!=200:
                    raise ValueError('Checkpoint upload not accepted')
        except Exception:
            raise RuntimeError('Checkpoint upload failed; no further dispatch') from None
        return hashlib.sha256(data).hexdigest()

def acknowledge(root,ackdir,record_path,upload_fn):
    record=json.loads(record_path.read_text())
    if record['status']!='compute-intent':
        return False
    digest=hashlib.sha256(record_path.read_bytes()).hexdigest()
    filename=f"{record['binding']}-{record['attempt']:08d}.json"
    target=ackdir/filename
    if target.exists():
        return False
    upload_fn(root)  # The public intent must survive host/root-volume deletion.
    ackdir.mkdir(parents=True,exist_ok=True)
    payload={'recordPath':str(record_path.relative_to(root)),
             'recordSha256':digest,'binding':record['binding']}
    temporary=target.with_suffix('.tmp')
    with temporary.open('x') as stream:
        json.dump(payload,stream);stream.flush();os.fsync(stream.fileno())
    temporary.replace(target)
    return True

def fail_cleanup(root,url,container_name):
    # Attempt both actions even if Docker is unresponsive. The independent host
    # shutdown/watchdog is still required; preserve the original failure.
    try:
        subprocess.run(['docker','rm','-f',container_name],capture_output=True,timeout=30)
    except Exception:
        pass
    try:
        upload(root,url)
    except Exception:
        pass


def supervise(root,ackdir,command,deadline,url,container_name):
    if command[:2]!=['docker','run'] or '--network=none' not in command or '--read-only' not in command:
        raise ValueError('Isolated Docker command required')
    if '--name='+container_name not in command:
        raise ValueError('Bound container identity required')
    if not any('@sha256:' in word for word in command):
        raise ValueError('Pinned image required')
    root.mkdir(parents=True,exist_ok=True);ackdir.mkdir(parents=True,exist_ok=True)
    while deadline-time.time()>1000:
        # Preparation never computes. A prepared record surviving an interrupted
        # wrapper is uncertain and must not be automatically executed again.
        try:
            prepared=subprocess.run(command+['prepare'],capture_output=True,text=True,timeout=120)
            if prepared.returncode:
                raise RuntimeError('Range preparation failed; reconcile')
            result=json.loads(prepared.stdout)
            upload(root,url)
        except BaseException:
            fail_cleanup(root,url,container_name)
            raise
        if result['status']!='prepared':
            return result
        execute=command+['execute','--attempt',str(result['attempt'])]
        with tempfile.TemporaryDirectory(prefix='qsb-invocation-') as tmp:
            stdout=Path(tmp)/'stdout';stderr=Path(tmp)/'stderr'
            with stdout.open('w') as output, stderr.open('w') as errors:
                process=subprocess.Popen(execute,stdout=output,stderr=errors)
                started=time.monotonic()
                try:
                    while process.poll() is None:
                        if time.time()>=deadline-90 or time.monotonic()-started>960:
                            raise TimeoutError('Invocation deadline reached')
                        for path in sorted(root.glob('range-*/record.json')):
                            acknowledge(root,ackdir,path,lambda p:upload(p,url))
                        time.sleep(.25)
                    if process.returncode:
                        raise RuntimeError('Range execution failed; preserve evidence and reconcile')
                except BaseException:
                    fail_cleanup(root,url,container_name)
                    try:
                        process.wait(timeout=30)
                    except Exception:
                        process.kill()
                    raise
            upload(root,url)  # Completion is checkpointed before another invocation.
            result=json.loads(stdout.read_text())
            if result['status']!='complete':
                return result
    upload(root,url)
    return {'status':'deadline-stop'}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    for name in ('output','acks','command','upload-url-file'):
        parser.add_argument('--'+name,type=Path,required=True)
    parser.add_argument('--deadline',type=int,required=True)
    parser.add_argument('--container-name',required=True)
    args=parser.parse_args()
    # URL is a capability: never include it in state, stdout, exceptions or bundles.
    url=args.upload_url_file.read_text().strip()
    result=supervise(args.output.resolve(),args.acks.resolve(),json.loads(args.command.read_text()),args.deadline,url,args.container_name)
    print(json.dumps(result))

if __name__=='__main__':main()
