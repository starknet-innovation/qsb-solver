"""Fixed saved-record verification; original predicates and public exporter unchanged."""
import contextlib,hashlib,io,json,os,pathlib,re,resource,sys,tempfile,time
from types import SimpleNamespace
ROOT=pathlib.Path(os.environ['QSB_PUBLIC_VERDICT_FIXTURES']).resolve() if 'QSB_PUBLIC_VERDICT_FIXTURES' in os.environ else None
REPO=pathlib.Path(__file__).resolve().parents[2]
sys.dont_write_bytecode=True
sys.path.insert(0,str(REPO/'experiments/generic-sha-vector'))
from ordered_verdicts import first_verified

def initialize():
    if ROOT is None:raise ValueError('QSB_PUBLIC_VERDICT_FIXTURES is required')
    plan=json.loads(pathlib.Path(__file__).with_name('first-verdict-fixture-lock.json').read_text())
    for name,want in plan['files'].items():
        p=ROOT/name if name=='event.json' else ROOT/'reference'/name
        if hashlib.sha256(p.read_bytes()).hexdigest()!=want:raise ValueError('input drift')
    if {p.name for p in (ROOT/'reference').iterdir()} != set(plan['files'])-{'event.json'}:
        raise ValueError('unexpected reference directory contents')
    if (ROOT/'pipeline').exists():raise ValueError('unexpected sibling import directory')
    sys.path.insert(0,str(ROOT/'reference'))
    global handler
    import handler

def check_prepared(directory,digests):
    root=pathlib.Path(directory)
    for name,want in digests.items():
        p=root/name
        if p.stat().st_mode & 0o222:raise ValueError('prepared input is writable')
        if hashlib.sha256(p.read_bytes()).hexdigest()!=want:raise ValueError('prepared input drift')

def initialize_prepared(directory,digests,event):
    initialize();check_prepared(directory,digests)
    global prepared
    prepared=(directory,event)

def evaluate(record):
    directory,event=prepared
    if not re.fullmatch(r'indices=\d+(?:,\d+){8}\n',record):raise ValueError('unexpected fixed record')
    values=[int(x) for x in record.strip().split('=')[1].split(',')]
    if len(set(values))!=9 or min(values)<0 or max(values)>=150:raise ValueError('invalid fixed indices')
    args=SimpleNamespace(work_dir=directory,funding_txid=event['manifest']['funding']['txid'],
                         sequence=event['sequence'],locktime=event['locktime'],round=1,
                         indices=','.join(map(str,sorted(149-i for i in values))))
    with contextlib.redirect_stdout(io.StringIO()):
        return handler.verify_hit.verify_digest(args)

def shared(event,workers):
    with tempfile.TemporaryDirectory(prefix='public-verification-') as directory:
        root=pathlib.Path(directory);original=handler.pipeline.cmd_export
        def capture(args):
            original(args)
            for name in ('qsb_state.json','gpu_digest_r1_params.json'):
                (root/name).write_bytes(pathlib.Path(name).read_bytes())
                (root/name).chmod(0o444)
        handler.pipeline.cmd_export=capture
        try:
            exported=handler.handler(dict(event,action='export'))
            if 'parameterSha256' not in exported:raise ValueError('export failed')
        finally:handler.pipeline.cmd_export=original
        digests={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in root.iterdir()}
        selected=first_verified(evaluate,event['candidates'],workers,initialize_prepared,(directory,digests,event))
        check_prepared(directory,digests)
        if selected['acceptedIndex'] is not None:
            record=event['candidates'][selected['acceptedIndex']]
            values=[int(x) for x in record.strip().split('=')[1].split(',')]
            result={'valid':True,'indices':sorted(149-i for i in values)}
        else:
            result={'valid':False}
            if selected['derOnly']:result['derOnly']=True
        return result,digests

def main():
    arm,count,target=sys.argv[1:];count=int(count)
    if arm not in ('serial','prepared1','parallel4') or count not in (1,32):
        raise ValueError('only fixed experiment modes and counts are permitted')
    initialize();event=json.loads((ROOT/'event.json').read_text())
    if event['stage']!='round1':raise ValueError('wrong frozen stage')
    event['candidates']=event['candidates'][:count];start=time.perf_counter()
    if arm=='serial':result=handler.handler(event);digests=None
    else:result,digests=shared(event,1 if arm=='prepared1' else 4)
    elapsed=time.perf_counter()-start
    own=resource.getrusage(resource.RUSAGE_SELF);children=resource.getrusage(resource.RUSAGE_CHILDREN)
    row=dict(arm=arm,count=count,result=result,handlerAndSchedulingSeconds=elapsed,preparedDigests=digests,cpuSeconds=own.ru_utime+own.ru_stime+children.ru_utime+children.ru_stime)
    with pathlib.Path(target).open('x') as f:json.dump(row,f,indent=2);f.flush();os.fsync(f.fileno())

if __name__=='__main__':main()
