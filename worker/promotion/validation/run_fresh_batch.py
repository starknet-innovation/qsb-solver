"""Bounded single-GPU fresh search batch; public requests/results only.

Requires an external 30-minute pod deletion watchdog. No CPU verification or
whole-proof claim is made here. The operator persists and verifies each result.
"""
import hashlib
import http.server
import json
import os
from pathlib import Path
import tempfile
import threading
import time
import uuid

PIN='4602c9845d7db1336b5ad00d67348063dce2c164bed3005ba18624f8c3dc6fa7'
SUB='1c7d6b5906e95c12f07faf08f93cfe5ca920974c9cb936909548b81b82dade3a'
COMMIT='bef76bf9aec123d95fdff53fb839a0c44f378927'
ALLOWED={'protocol','stage','parameterBase64','parameterSha256','manifestHash','attempt','sequence','locktime','kernelCommit','searchVersion'}


def validate_batch(value):
    if set(value) != {'batchId','request','maxAttempts'}:
        raise ValueError('Unexpected batch fields')
    if str(uuid.UUID(value['batchId'])) != value['batchId']:
        raise ValueError('Invalid batch ID')
    request=value['request']
    if not isinstance(request,dict) or set(request)-ALLOWED:
        raise ValueError('Only public worker request fields permitted')
    if request.get('kernelCommit') != COMMIT:
        raise ValueError('Wrong frozen source')
    if type(value['maxAttempts']) is not int or not 1 <= value['maxAttempts'] <= 64:
        raise ValueError('Invalid bounded attempt count')
    if type(request.get('attempt')) is not int or request['attempt'] < 0:
        raise ValueError('Invalid first attempt')
    return request


def run_batch(batch, invoke, work_range, publish, clock=time.monotonic):
    request=validate_batch(batch)
    deadline=clock()+1350
    state={'batchId':batch['batchId'],'status':'running','request':request,'results':[],
           'activeAttempt':None,'candidateRequiresCpuVerification':False}
    publish(state)
    for offset in range(batch['maxAttempts']):
        # Installed handler has an840second timeout plus termination grace.
        if deadline-clock()<860:break
        data=dict(request,attempt=request['attempt']+offset)
        expected=work_range(data['stage'],data['attempt'])
        state['activeAttempt']=data['attempt'];publish(state)
        result=invoke({'input':data})
        if any(result.get(k)!=data[k] for k in ['stage','manifestHash','attempt','kernelCommit']):
            raise ValueError('Returned identity mismatch')
        if (result.get('verified') is not False or not isinstance(result.get('candidates'),list)
                or any(not isinstance(c,str) or len(c)>=16384 for c in result['candidates'])):
            raise ValueError('Malformed worker result')
        if result.get('workRange')!=expected:
            raise ValueError('Returned range mismatch')
        state['results'].append(result);state['activeAttempt']=None;publish(state)
        if result.get('status')!='completed' or result.get('checkpoint')!='range-complete':
            state['status']='failed';break
        if result.get('candidates'):
            state['status']='candidate';state['candidateRequiresCpuVerification']=True;break
    else:state['status']='batch-complete'
    if state['status']=='running':state['status']='bounded-stop'
    publish(state)
    return state


def main():
    import handler
    from search_ranges import work_range
    # Never repeat paid work on a container restart. The operator reconciles it.
    batch=json.loads(os.environ['QSB_PUBLIC_BATCH'])
    validate_batch(batch)
    marker=Path('/tmp/qsb-fresh-batch-started')
    try:
        with marker.open('x') as record:record.write(batch['batchId']+'\n')
    except FileExistsError:
        print('QSB_FRESH_BATCH restart-refused',flush=True)
        time.sleep(1600)
        return
    request=validate_batch(batch)
    binding=handler.release_binding()
    if binding['solverCommit']!=COMMIT or binding['files']['pinning']!=PIN or binding['files']['subset']!=SUB:
        raise ValueError('Wrong installed binaries')
    # Validate payload before publishing or executing it.
    handler.historical_handler.PINNED_KERNEL=COMMIT
    handler.historical_handler.validate_request(request)
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);target=root/'result.json'
        def publish(state):
            temp=root/'result.tmp';temp.write_text(json.dumps(state,sort_keys=True)+'\n');temp.replace(target)
        class Serve(http.server.BaseHTTPRequestHandler):
            def do_GET(self):
                if self.path!='/result.json' or not target.exists():self.send_error(404);return
                raw=target.read_bytes();self.send_response(200)
                self.send_header('Content-Type','application/json');self.send_header('Content-Length',str(len(raw)))
                self.end_headers();self.wfile.write(raw)
            def log_message(self,*args):pass
        server=http.server.ThreadingHTTPServer(('0.0.0.0',8000),Serve)
        thread=threading.Thread(target=server.serve_forever,daemon=True);thread.start()
        try:
            try:
                state=run_batch(batch,handler.handler,work_range,publish)
            except Exception as error:
                state=json.loads(target.read_text()) if target.exists() else {'batchId':batch['batchId'],'results':[]}
                state['status']='operator-reconciliation-required'
                state['errorType']=type(error).__name__
                publish(state)
            print('QSB_FRESH_BATCH',state['status'],hashlib.sha256(target.read_bytes()).hexdigest(),flush=True)
            time.sleep(180)  # bounded result retrieval; external watchdog remains required
        finally:server.shutdown();server.server_close()


if __name__=='__main__':main()
