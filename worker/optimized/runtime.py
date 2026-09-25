"""One-request compute-only runtime. Independent verification belongs to qsb-app."""
import hashlib,json,pathlib,sys,contextlib,io
ROOT=pathlib.Path(__file__).resolve().parent

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def bindings():
    raw=(ROOT/'runtime-binding.json').read_bytes();d=json.loads(raw)
    for name,want in d['files'].items():
        p=ROOT/name
        if p.is_symlink() or '..' in pathlib.Path(name).parts or pathlib.Path(name).is_absolute() or sha(p)!=want:raise ValueError('Runtime artifact mismatch')
    return d,hashlib.sha256(raw).hexdigest()
def handle(e):
    d,h=bindings()
    if e=={'action':'describe'}:return {'runtimeHash':h,'binding':d,'status':'HOLD'}
    if type(e)!=dict or set(e)!={'action','runtimeHash','request'} or e.get('runtimeHash')!=h or e.get('action')!='compute':raise ValueError('Only bound compute requests accepted')
    sys.path.insert(0,str(ROOT/'candidate'))
    import candidate_handler
    return {'runtimeHash':h,'output':candidate_handler.handler({'input':e['request']})}

if __name__=='__main__':
    try:
        raw=sys.stdin.buffer.read(2000001)
        if len(raw)>2000000:raise ValueError('Request too large')
        # Do not let solver diagnostics pollute the JSON transport.
        with contextlib.redirect_stdout(io.StringIO()):result=handle(json.loads(raw))
        print(json.dumps({'ok':True,'result':result}))
    except Exception as error:
        print(json.dumps({'ok':False,'error':type(error).__name__+': '+str(error)}));sys.exit(2)
