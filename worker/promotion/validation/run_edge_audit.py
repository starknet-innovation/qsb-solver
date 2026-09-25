"""Bounded native pin replay and diagnostic edges; no signing or range credit."""
import base64,hashlib,json,math,os,re,signal,subprocess,sys,tempfile,time
from pathlib import Path
PIN='4602c9845d7db1336b5ad00d67348063dce2c164bed3005ba18624f8c3dc6fa7'
SUB='1c7d6b5906e95c12f07faf08f93cfe5ca920974c9cb936909548b81b82dade3a'


def unrank(rank):
    out=[];lo=0
    for k in range(9,0,-1):
        for v in range(lo,150):
            n=math.comb(149-v,k-1)
            if rank<n:out.append(v);lo=v+1;break
            rank-=n
    return out


def run(binary,params,args,deadline,env=None):
    with tempfile.TemporaryDirectory() as tmp:
        root=Path(tmp);(root/'params.bin').write_bytes(base64.b64decode(params,validate=True))
        clean={k:v for k,v in os.environ.items() if not k.startswith('QSB_AUDIT_')};clean.update(env or {})
        p=subprocess.Popen([str(binary),'params.bin',*args],cwd=root,env=clean,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,start_new_session=True)
        try:log,_=p.communicate(timeout=max(.1,min(90,deadline-time.monotonic())))
        except subprocess.TimeoutExpired:
            os.killpg(p.pid,signal.SIGKILL);p.communicate();raise
        hits={p.name:p.read_text() for p in (root/'results').glob('*hit*.txt')}
        return dict(exit=p.returncode,log=log,hits=hits)


def main():
    root=Path(sys.argv[1]);output=Path(sys.argv[2]);deadline=time.monotonic()+1100
    for name,expected in [('pinning',PIN),('subset',SUB)]:
        if hashlib.sha256((Path('/opt/qsb')/name).read_bytes()).hexdigest()!=expected:raise ValueError('wrong image binary')
    receipt=json.loads((root/'receipt.json').read_text())
    if receipt['unmodifiedBinarySha256']!=SUB:raise ValueError('wrong unmodified subset identity')
    expected={n+s for n in ['capacity','forced-exception','detected-exception'] for s in ['', '.diff']}
    if set(receipt['files'])!=expected:raise ValueError('wrong artifact inventory')
    for n,h in receipt['files'].items():
        if hashlib.sha256((root/n).read_bytes()).hexdigest()!=h:raise ValueError('artifact mismatch')
        if not n.endswith('.diff'):(root/n).chmod(0o700)
    fixture=json.loads((root/'fixtures.json').read_text());pin=fixture['pinning']
    if hashlib.sha256(base64.b64decode(pin['parameterBase64'],validate=True)).hexdigest()!=pin['parameterSha256']:raise ValueError('pin parameters mismatch')
    row=run('/opt/qsb/pinning',pin['parameterBase64'],['0','1','0','single_hash',f"seq_start={pin['sequence']}",'seq_count=1',f"lt_start={pin['locktime']}",'lt_count=1'],deadline)
    if row['exit'] or 'Done:' not in row['log'] or row['hits']!={'pinning_hit_0.txt':pin['expected']}:raise ValueError('known pin replay failed: '+str(row))
    result=dict(pinning=row,receipt=receipt,capacity=[],exceptions=[])
    print('PIN_REPLAY PASS',flush=True)
    for count in [0,1,63,64,65,1024,1025]:
        args=['0','2147483648','500000000','1','0','single_hash','rank_start=7','rank_count=1100']
        row=run(root/'capacity',fixture['ordinaryParams'],args,deadline,{'QSB_AUDIT_HITS':str(count)})
        if row['exit']!=(2 if count>64 else 0) or f'DEVICE_COUNT {count} CANARIES_OK' not in row['log']:raise ValueError('capacity exit/count failed')
        records=[list(map(int,line.split()[1:])) for line in row['log'].splitlines() if line.startswith('DEVICE_REC ')]
        if len(records)!=min(count,1024) or len({r[0] for r in records})!=len(records):raise ValueError('capacity multiplicity failed')
        for idx,*indices in records:
            if not 0<=idx<count or indices!=unrank(7+idx):raise ValueError('capacity retained combination mismatch')
        if count>64:
            if 'Done enum:' in row['log'] or row['hits']:raise ValueError('overflow wrongly completed')
        elif 'Done enum:' not in row['log'] or sum(v.count('indices=') for v in row['hits'].values())!=count:raise ValueError('capacity publication mismatch')
        result['capacity'].append(dict(count=count,**row));print('CAPACITY',count,'PASS',flush=True)
    for mode,count in [('forced-exception',7),('forced-exception',64),('forced-exception',65),('detected-exception',7)]:
        row=run(root/mode,fixture['exceptionParams'],['0','2147483648','500000000','1','0','single_hash','rank_start=7',f'rank_count={count}'],deadline)
        if row['exit']!=(2 if count>64 else 0):raise ValueError('exception exit failed')
        records=[line for line in row['log'].splitlines() if line.startswith('EXACT ')]
        if count>64:
            if 'Done enum:' in row['log'] or row['hits']:raise ValueError('exception overflow completed')
        elif 'Done enum:' not in row['log'] or len(records)!=count or row['hits']:raise ValueError('exception handoff multiplicity/predicate failed')
        result['exceptions'].append(dict(mode=mode,count=count,**row));print('EXCEPTION',mode,count,'EXECUTED',flush=True)
    output.write_text(json.dumps(result,indent=2)+'\n');print('QSB_REGRESSION_PASS',hashlib.sha256(output.read_bytes()).hexdigest(),flush=True)

if __name__=='__main__':main()
