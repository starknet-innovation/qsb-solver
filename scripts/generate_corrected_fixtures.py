"""Synthetic nonexistent-outpoint compatibility vectors; writes public data only."""
import sys,tempfile,os,json,contextlib,io,hashlib
from pathlib import Path
from types import SimpleNamespace
root=Path(sys.argv[1]).resolve(); out=Path(sys.argv[2]).resolve();out.mkdir(exist_ok=True)
sys.path[:0]=[str(root/'public/qsb'),str(root/'worker/cpu')]
import bridge,qsb_pipeline as p
from bitcoin_tx import find_and_delete, Transaction, TxIn, TxOut
assert bridge.SCRIPT_VERSION == "qsb-config-a-cmsverify-v1", "Corrected app reference required"
with tempfile.TemporaryDirectory() as tmp:
 os.chdir(tmp)
 with contextlib.redirect_stdout(io.StringIO()):p.cmd_setup(SimpleNamespace(config='A',seed=719))
 state=json.loads(Path('qsb_state.json').read_text());state['scriptVersion']='qsb-config-a-cmsverify-v1'
 public={k:state[k] for k in bridge.PUBLIC_FIELDS};public['round_sigs']=[{k:r[k] for k in ('r','s','sig')} for r in state['round_sigs']]
 Path('qsb_state.json').write_text(json.dumps(public))
 args=SimpleNamespace(funding_txid='11'*32,funding_vout=0,funding_value=100000,extra_input_txid='22'*32,extra_input_vout=1,extra_input_value=10000,extra_input_sequence=0xfffffffe,version=1,sequence=0x80000000,locktime=500000000,output_value=90000,output_address='00'*20)
 p.p2pkh_script=lambda _:bytes.fromhex('0014'+'33'*20)
 with contextlib.redirect_stdout(io.StringIO()):p.cmd_export(args)
 for name in ('pinning.bin','digest_r1.bin','digest_r2.bin','gpu_pinning_params.json','gpu_digest_r1_params.json','gpu_digest_r2_params.json'):(out/name).write_bytes(Path(name).read_bytes())
 (out/'public-state.json').write_text(json.dumps(public,indent=2)+'\n')
 vectors=[]
 for ri in range(2):
  for subset in (list(range(9)),list(range(141,150)),[0,3,11,38,64,71,98,132,149]):
   for sequence,locktime in ((0x80000000,500000000),(0xffffffff,1744599999)):
    script=find_and_delete(bytes.fromhex(public['full_script_hex']),bytes.fromhex(public['round_sigs'][ri]['sig']))
    for idx in subset:script=find_and_delete(script,bytes.fromhex(public['dummy_sigs'][ri][idx]))
    tx=Transaction(version=1,locktime=locktime)
    tx.add_input(TxIn(bytes.fromhex('22'*32),1,b'',0xfffffffe));tx.add_input(TxIn(bytes.fromhex('11'*32),0,b'',sequence));tx.add_output(TxOut(90000,bytes.fromhex('0014'+'33'*20)))
    vectors.append(dict(round=ri+1,subsetPoolIndices=subset,sequence=sequence,locktime=locktime,scriptCodeSha256=hashlib.sha256(script).hexdigest(),sighash=tx.sighash(1,script,1).to_bytes(32,'big').hex()))
 (out/'sighash-vectors.json').write_text(json.dumps(vectors,indent=2)+'\n')

sources={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for folder in ('public/qsb','worker/cpu') for f in sorted((root/folder).glob('*.py'))}
files={f.name:hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted(out.iterdir()) if f.name!='provenance.json'}
(out/'provenance.json').write_text(json.dumps(dict(scriptVersion='qsb-config-a-cmsverify-v1',generatorCommit='b22f81c093488d09b9cd59c171c79b6c40812cf1',seed=719,purpose='synthetic nonexistent-outpoint CPU compatibility vectors; no GPU or consensus qualification',sourceFiles=sources,files=files),indent=2)+'\n')
