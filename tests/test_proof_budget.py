import concurrent.futures
import importlib.util
from pathlib import Path
import tempfile
import unittest
import uuid
spec=importlib.util.spec_from_file_location('proof_budget',Path(__file__).resolve().parents[1]/'ops/fresh-proof/budget.py')
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

class ProofBudget(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
        self.path=Path(self.tmp.name)/'budget.sqlite'
        self.campaign=dict(campaignId=str(uuid.uuid4()),requestHash='a'*64,candidateSource='b'*40,imageDigest='c'*64)
        self.b=m.Budget.create(self.path,self.campaign)
        self.request=dict(region='eu-west-1',instanceType='g5.xlarge',maxCount=1)

    def reserve(self, amount=2_000_000):
        intent=str(uuid.uuid4());self.b.reserve(intent,self.request,amount);return intent

    def evidence(self,intent):
        resource=dict(instanceId='i-test',volumeIds=['vol-test'],clientToken=intent)
        self.b.attach(intent,self.request,resource)
        return dict(instanceId='i-test',instanceState='terminated',volumeIds=['vol-test'],
          volumesRemaining=0,securityGroupsRemaining=0,schedulesRemaining=0,functionsRemaining=0,
          rolesRemaining=0,instanceProfilesRemaining=0,receiptSha256='d'*64)

    def test_race_admits_one_intent(self):
        def attempt(_):
            try:self.reserve();return True
            except ValueError:return False
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            self.assertEqual(sum(pool.map(attempt,range(8))),1)
        self.assertEqual(self.b.snapshot()['committedMicroUsd'],2_000_000)

    def test_unknown_survives_reopen_and_blocks_paid_replacement(self):
        intent=self.reserve();self.b=m.Budget(self.path,self.campaign)
        with self.assertRaises(ValueError):self.reserve()
        with self.assertRaises(ValueError):self.b.settle(intent,{})
        self.assertEqual(self.b.snapshot()['unresolved'],[intent])

    def test_cleanup_keeps_entire_allowance_charged(self):
        intent=self.reserve();e=self.evidence(intent)
        self.b.settle(intent,e)
        self.assertEqual(self.b.snapshot()['committedMicroUsd'],2_000_000)
        self.assertEqual(self.b.snapshot()['availableMicroUsd'],178_000_000)
        self.reserve()
        with self.assertRaises(ValueError):self.b.settle(intent,e)

    def test_exact_admission_boundary_preserves_headroom(self):
        intent=self.reserve(180_000_000);self.b.settle(intent,self.evidence(intent))
        self.assertEqual(self.b.snapshot()['availableMicroUsd'],0)
        with self.assertRaises(ValueError):self.reserve(1)

    def test_rejects_excess_without_partial_intent(self):
        with self.assertRaises(ValueError):self.reserve(180_000_001)
        self.assertEqual(self.b.snapshot()['committedMicroUsd'],0)

    def test_cleanup_must_bind_instance_volume_and_all_remaining_resources(self):
        intent=self.reserve();e=self.evidence(intent)
        for key,value in [('instanceId','i-other'),('volumeIds',[]),('volumesRemaining',1),('rolesRemaining',False),('instanceState','shutting-down')]:
            with self.subTest(key=key),self.assertRaises(ValueError):self.b.settle(intent,dict(e,**{key:value}))
        self.assertEqual(self.b.snapshot()['unresolved'],[intent])

    def test_request_frozen_and_late_attachment_preserved(self):
        intent=self.reserve()
        resource=dict(instanceId='i-test',volumeIds=['vol-test'],clientToken=intent)
        with self.assertRaises(ValueError):self.b.attach(intent,dict(self.request,maxCount=2),resource)
        self.b.attach(intent,self.request,resource)
        with self.assertRaises(ValueError):self.b.attach(intent,self.request,resource)
        with self.assertRaises(ValueError):self.b.reserve(intent,self.request,2_000_000)

    def test_no_reinitialize_or_rebind_or_missing_database(self):
        with self.assertRaises(FileExistsError):m.Budget.create(self.path,self.campaign)
        with self.assertRaises(ValueError):m.Budget(self.path,dict(self.campaign,imageDigest='e'*64))
        with self.assertRaises(FileNotFoundError):m.Budget(self.path.with_name('missing'),self.campaign)
        alias=self.path.with_name('alias');alias.symlink_to(self.path)
        with self.assertRaises(ValueError):m.Budget(alias,self.campaign)

    def test_rejects_fractional_negative_boolean_allowances(self):
        for amount in [True,0,-1,1.2,'200',float('nan')]:
            with self.subTest(amount=amount),self.assertRaises(ValueError):self.reserve(amount)

    def test_existing_handle_rejects_replaced_ledger(self):
        self.reserve(180_000_000)
        self.path.rename(self.path.with_name('preserved.sqlite'))
        m.Budget.create(self.path,dict(self.campaign,campaignId=str(uuid.uuid4())))
        with self.assertRaises(ValueError):self.reserve(1)
        with self.assertRaises(ValueError):self.b.snapshot()

    def test_each_transaction_rechecks_authorization(self):
        import sqlite3
        from contextlib import closing
        with closing(sqlite3.connect(self.path)) as db:
            db.execute('UPDATE campaign SET maximum=400000000');db.commit()
        with self.assertRaises(ValueError):self.reserve()
