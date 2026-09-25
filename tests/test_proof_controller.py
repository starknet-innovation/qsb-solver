import importlib.util
from datetime import datetime, timezone, timedelta
import json
from pathlib import Path
import sys
import tempfile
import time
import unittest
import uuid
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ops/fresh-proof'))
spec=importlib.util.spec_from_file_location('proof_control',ROOT/'ops/fresh-proof/control.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class Backend:
    def __init__(self):self.paid=[];self.error=None;self.instances=[];self.remaining=False
    def main(self,proof):
        mode=sys.argv[1];path=Path(sys.argv[3])
        if mode=='prepare':
            s=dict(token=proof.token,name='qsb-bench-'+proof.token[:8],controllerCommit=proof.ledger.get(proof.token)['request']['controllerCommit'],proofBudget=proof.binding,phase='preparing',securityGroup='sg-original',functionArn='arn:fixture')
            self.save(path,s)
        else:s=json.loads(path.read_text())
        proof.check(path,s,mode)
        assert proof.ledger.snapshot()['committedMicroUsd']>=m.ALLOWANCE
        self.paid.append(mode)
        s['phase']={'prepare':'prepared','arm':'armed','launch':'launch-intent','cleanup':'cleaned'}[mode];self.save(path,s)
        if self.error:raise RuntimeError(self.error)
        if mode=='launch':
            s.update(phase='launched',instanceId='i-test');self.save(path,s)
            self.instances=[dict(InstanceId='i-test',ClientToken=proof.token,LaunchTime=datetime.now(timezone.utc).isoformat(),State=dict(Name='running'),BlockDeviceMappings=[dict(Ebs=dict(VolumeId='vol-test'))])]
    def save(self,path,s):path.write_text(json.dumps(s))
    def aws(self,service,operation,**kwargs):
        if service=='sts':return dict(Account='905846953990')
        if operation=='describe-instances':return dict(Reservations=[dict(Instances=self.instances)] if self.instances else [])
        key={'describe-volumes':'Volumes','describe-security-groups':'SecurityGroups','list-schedules':'Schedules','list-functions':'Functions','list-roles':'Roles','list-instance-profiles':'InstanceProfiles'}[operation]
        return {key:([{}] if self.remaining and key=='Volumes' else [])}

class ControllerTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name)/'state.json'
        self.campaign=dict(campaignId=str(uuid.uuid4()),requestHash='a'*64,candidateSource=m.SOURCE,imageDigest=m.IMAGE)
        self.ledger=m.Budget.create(self.path.with_name('budget.sqlite'),self.campaign)
        self.backend=Backend()
        patched=patch.object(m,'source_identity',return_value='test-controller');patched.start();self.addCleanup(patched.stop)
    def quote(self):return dict(observedAt=int(time.time()),allowanceMicroUsd=m.ALLOWANCE)
    def execute(self,mode):return m.execute(mode,self.path,self.ledger,self.campaign,self.quote,self.backend)
    def launch(self):
        for mode in ['prepare','arm','launch']:self.execute(mode)
    def test_reserves_before_paid_prepare_and_retains_after_cleanup(self):
        self.launch();self.assertEqual(self.backend.paid,['prepare','arm','launch'])
        self.backend.instances[0]['State']['Name']='terminated'
        self.execute('cleanup');m.reconcile(self.path,self.ledger,self.campaign,self.backend)
        self.assertEqual(self.ledger.snapshot()['committedMicroUsd'],m.ALLOWANCE)
        self.assertFalse(self.ledger.snapshot()['unresolved'])
    def test_repeated_prepare_never_calls_provider_twice(self):
        self.execute('prepare')
        with self.assertRaises(ValueError):self.execute('prepare')
        self.assertEqual(self.backend.paid,['prepare'])
    def test_unknown_launch_stays_reserved_and_cannot_repeat(self):
        self.execute('prepare');self.execute('arm');self.backend.error='read timeout; response unknown'
        with self.assertRaises(RuntimeError):self.execute('launch')
        with self.assertRaises((ValueError,FileExistsError)):self.execute('launch')
        with self.assertRaises(ValueError):m.reconcile(self.path,self.ledger,self.campaign,self.backend)
        self.assertEqual(self.backend.paid,['prepare','arm','launch'])
        self.assertEqual(len(self.ledger.snapshot()['unresolved']),1)
    def test_explicit_rejection_only_settles_after_cloud_cleanup(self):
        self.execute('prepare');self.execute('arm')
        self.backend.error='An error occurred (InsufficientInstanceCapacity) when calling the RunInstances operation'
        with self.assertRaises(RuntimeError):self.execute('launch')
        self.backend.error=None;self.execute('cleanup')
        m.reconcile(self.path,self.ledger,self.campaign,self.backend)
        self.assertFalse(self.ledger.snapshot()['unresolved'])
        self.assertEqual(self.ledger.snapshot()['committedMicroUsd'],m.ALLOWANCE)
    def test_live_instance_and_orphan_volume_block_settlement(self):
        self.launch()
        with self.assertRaises(ValueError):m.reconcile(self.path,self.ledger,self.campaign,self.backend)
        self.backend.instances[0]['State']['Name']='terminated';self.backend.remaining=True
        with self.assertRaises(ValueError):m.reconcile(self.path,self.ledger,self.campaign,self.backend)
    def test_late_identity_reconciles_without_resubmitting(self):
        self.execute('prepare');self.execute('arm');self.backend.error='timeout'
        with self.assertRaises(RuntimeError):self.execute('launch')
        token=json.loads(self.path.read_text())['token'];self.backend.instances=[dict(InstanceId='i-late',ClientToken=token,LaunchTime=datetime.now(timezone.utc).isoformat(),State=dict(Name='terminated'),BlockDeviceMappings=[dict(Ebs=dict(VolumeId='vol-late'))])]
        m.reconcile(self.path,self.ledger,self.campaign,self.backend)
        self.assertEqual(self.backend.paid,['prepare','arm','launch'])
        self.assertFalse(self.ledger.snapshot()['unresolved'])
    def test_exhausted_budget_and_stale_quote_prevent_all_paid_calls(self):
        token=str(uuid.uuid4());self.ledger.reserve(token,{},180_000_000)
        with self.assertRaises(ValueError):self.execute('prepare')
        self.assertEqual(self.backend.paid,[])
    def test_controller_cannot_bypass_guard_for_proof_state(self):
        self.execute('prepare')
        def aws(service,operation,**kw):
            self.assertEqual((service,operation),('sts','get-caller-identity'));return dict(Account='905846953990')
        def git(cmd,**kw):return b'' if 'status' in cmd else 'fixed\n'
        with patch.object(m.AWS,'aws',aws),patch.object(m.AWS.subprocess,'check_output',git),patch.object(sys,'argv',['control','arm','--state',str(self.path)]):
            with self.assertRaisesRegex(ValueError,'budgeted controller'):m.AWS.main()

    def test_overrun_stays_reserved_even_after_terminal_cleanup(self):
        self.launch();self.backend.instances[0]['State']['Name']='terminated'
        self.backend.instances[0]['LaunchTime']=(datetime.now(timezone.utc)-timedelta(hours=2)).isoformat()
        with self.assertRaisesRegex(ValueError,'reserved hour'):m.reconcile(self.path,self.ledger,self.campaign,self.backend)
        self.assertTrue(self.ledger.snapshot()['unresolved'])
    def test_changed_cleanup_name_cannot_hide_resources(self):
        self.launch();self.backend.instances[0]['State']['Name']='terminated'
        s=json.loads(self.path.read_text());s['name']='unrelated-empty-prefix';self.path.write_text(json.dumps(s))
        with self.assertRaisesRegex(ValueError,'reserved token'):m.reconcile(self.path,self.ledger,self.campaign,self.backend)
    def test_frozen_scope_cannot_change(self):
        self.execute('prepare');token=json.loads(self.path.read_text())['token']
        self.ledger.bind_scope(token,dict(securityGroup='sg-original'))
        s=json.loads(self.path.read_text());s['securityGroup']='sg-other';self.path.write_text(json.dumps(s))
        with self.assertRaisesRegex(ValueError,'binding changed'):self.execute('arm')

    def test_stale_quote_rejects_before_reservation(self):
        stale=lambda:dict(observedAt=int(time.time())-301,allowanceMicroUsd=m.ALLOWANCE)
        with self.assertRaises(ValueError):m.execute('prepare',self.path,self.ledger,self.campaign,stale,self.backend)
        self.assertEqual(self.ledger.snapshot()['committedMicroUsd'],0)
    def test_existing_owner_blocks_second_controller(self):
        with m.owner_lock(self.ledger.path):
            with self.assertRaises(BlockingIOError):self.execute('prepare')
        self.assertEqual(self.backend.paid,[])
    def test_actual_controller_rejects_unreserved_before_first_mutation(self):
        guard=m.Guard(self.ledger,str(uuid.uuid4()),self.path,self.campaign);calls=[]
        def aws(service,operation,**kw):
            calls.append((service,operation));return dict(Account='905846953990')
        def git(cmd,**kw):return b'' if 'status' in cmd else 'fixed\n'
        with patch.object(m.AWS,'aws',aws),patch.object(m.AWS.subprocess,'check_output',git),patch.object(sys,'argv',['control','prepare','--state',str(self.path)]):
            with self.assertRaisesRegex(ValueError,'unknown budget intent'):m.AWS.main(proof=guard)
        self.assertEqual(calls,[('sts','get-caller-identity')])

class PriceTests(unittest.TestCase):
    def fetch(self,service,filters):
        rate,unit=('1.123','Hrs') if 'instanceType' in filters else (('0.088','GB-Mo') if service=='AmazonEC2' else ('0.005','Hrs'))
        p=dict(product=dict(attributes=filters),terms=dict(OnDemand={'x':dict(priceDimensions={'x':dict(unit=unit,beginRange='0',endRange='Inf',pricePerUnit=dict(USD=rate))})}))
        return dict(PriceList=[json.dumps(p)])
    def test_three_scope_bound_prices_and_full_allowance(self):
        q=m.price_quote(self.fetch);self.assertEqual(q['allowanceMicroUsd'],2_000_000);self.assertEqual(set(q['rates']),{'compute','storage','ipv4'})
    def test_missing_or_ambiguous_quote_rejects(self):
        for values in [[],[self.fetch('AmazonEC2',dict(instanceType='g5.xlarge'))['PriceList'][0]]*2]:
            with self.assertRaises(ValueError):m.price_quote(lambda *a:dict(PriceList=values))

    def test_above_ceiling_price_rejects(self):
        def expensive(service,filters):
            p=self.fetch(service,filters);item=json.loads(p['PriceList'][0])
            if 'instanceType' in filters:item['terms']['OnDemand']['x']['priceDimensions']['x']['pricePerUnit']['USD']='2.0'
            p['PriceList']=[json.dumps(item)];return p
        with self.assertRaises(ValueError):m.price_quote(expensive)
