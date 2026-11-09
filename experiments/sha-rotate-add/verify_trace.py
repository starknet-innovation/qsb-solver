"""Separate CPU/full-transaction verification; accepts only frozen public references."""
import hashlib
import json
from pathlib import Path
import sys
import tempfile
from run_pair import SUB, check_sample
from run_trace import FIXTURES, trace_records, unrank


def check_case(plan,row,state,params,emulate,Transaction,TxIn,TxOut,find_and_delete):
    records=trace_records(row['trace']['log'],plan['start'],plan['count'])
    for name in ['trace','exact']:
        check_sample(row[name],plan['count'],plan['start'])
    for rank in range(plan['start'],plan['start']+plan['count']):
        gpu=unrank(rank);indices=sorted(149-i for i in gpu)
        emulated=emulate(params,indices,sequence=plan['sequence'],locktime=plan['locktime'])
        stage=plan['stage']
        sc=find_and_delete(bytes.fromhex(state['full_script_hex']),bytes.fromhex(state['round_sigs'][stage-1]['sig']))
        for index in indices:sc=find_and_delete(sc,bytes.fromhex(state['dummy_sigs'][stage-1][index]))
        sp=params['spending_tx'];tx=Transaction(version=sp['version'],locktime=plan['locktime'])
        tx.add_input(TxIn(bytes.fromhex(sp['extra_input']['txid'])[::-1],sp['extra_input']['vout'],b'',sp['extra_input']['sequence']))
        tx.add_input(TxIn(bytes.fromhex(sp['qsb_input']['txid'])[::-1],sp['qsb_input']['vout'],b'',plan['sequence']))
        tx.add_output(TxOut(sp['output']['value'],bytes.fromhex(sp['output']['script_pubkey'])))
        if tx.sighash(1,sc,1).to_bytes(32,'big')!=emulated['sighash']:
            raise ValueError('full transaction/emulator mismatch')
        if {records[(gpu,b)] for b in [0,1]}!={c['puzzle_hash'].hex() for c in emulated['candidates']}:
            raise ValueError('CPU/GPU recovery hash mismatch')
    return dict(name=plan['name'],candidates=plan['count'],hashes=plan['count']*2)


def load_public(reference,fixtures):
    lock=json.loads(Path(__file__).with_name('cpu-reference-lock.json').read_text())
    data={}
    for name,want in lock['files'].items():
        kind,relative=name.split('/',1)
        path=(reference if kind=='reference' else fixtures)/relative
        raw=path.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=want:raise ValueError('public reference mismatch: '+name)
        data[name]=raw
    return data


def main():
    result_path,reference,fixtures,output=map(Path,sys.argv[1:5])
    if output.exists():raise ValueError('output already exists')
    result_raw=result_path.read_bytes();result=json.loads(result_raw)
    if result.get('status')!='native-completed-awaiting-cpu-verification' or result.get('candidateSha256')!=SUB or result.get('fixtureSha256')!=FIXTURES:
        raise ValueError('wrong native result binding or state')
    plan_raw=(Path(__file__).resolve().parents[2]/'worker/promotion/validation/trace-fixtures.json').read_bytes()
    if hashlib.sha256(plan_raw).hexdigest()!=FIXTURES:raise ValueError('plan mismatch')
    plans=json.loads(plan_raw)['cases']
    if [r['name'] for r in result['ranges']]!=[p['name'] for p in plans]:raise ValueError('native case inventory mismatch')
    data=load_public(reference,fixtures)
    # Copy only hash-verified modules into a fresh import root; no arbitrary sibling modules.
    with tempfile.TemporaryDirectory() as directory:
        root=Path(directory)
        for name,raw in data.items():
            if name.startswith('reference/'):(root/Path(name).name).write_bytes(raw)
        sys.path.insert(0,str(root))
        from gpu_emulator import emulate_digest_round
        from bitcoin_tx import Transaction,TxIn,TxOut,find_and_delete
        rows=[]
        for plan,row in zip(plans,result['ranges']):
            prefix='fixtures/'+plan['case']+'/'
            state=json.loads(data[prefix+'qsb_state.json'])
            params=json.loads(data[prefix+f"gpu_digest_r{plan['stage']}_params.json"])
            rows.append(check_case(plan,row,state,params,emulate_digest_round,Transaction,TxIn,TxOut,find_and_delete))
    summary=dict(status='passed',nativeResultSha256=hashlib.sha256(result_raw).hexdigest(),candidateSha256=SUB,
                 rows=rows,candidates=sum(r['candidates'] for r in rows),hashes=sum(r['hashes'] for r in rows),
                 freshWithdrawal=False,grantsRangeCredit=False,
                 scope='Diagnostic CPU/full-transaction differential plus separately sampled exact binary; not whole-domain proof')
    with output.open('x') as stream:json.dump(summary,stream,indent=2)
    print(json.dumps({k:v for k,v in summary.items() if k!='rows'}))


if __name__=='__main__':main()
