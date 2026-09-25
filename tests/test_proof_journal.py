import importlib.util
import json
from pathlib import Path
import sys
import uuid
import unittest
import test_proof_budget
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'ops/fresh-proof'))
from journal import Journal
spec=importlib.util.spec_from_file_location('journal_ranges',ROOT/'worker/search_ranges.py')
ranges=importlib.util.module_from_spec(spec);spec.loader.exec_module(ranges)

class JournalTests(unittest.TestCase):
    reserve=test_proof_budget.ProofBudget.reserve
    evidence=test_proof_budget.ProofBudget.evidence
    def setUp(self):
        test_proof_budget.ProofBudget.setUp(self)
        self.j=Journal(self.b);self.j.initialize('e'*64,'f'*64,self.campaign['campaignId'])
        self.batch=dict(batchId=str(uuid.uuid4()),maxAttempts=2,request=dict(stage='pinning',attempt=0,manifestHash='f'*64,parameterSha256='a'*64))
    def register(self):
        token=self.reserve();self.j.register(token,json.dumps(self.batch).encode(),lambda b:b['request']);return token
    def ready(self):
        token=self.register();e=self.evidence(token);self.j.claim_command(token)
        command=str(uuid.uuid4());self.j.attach_command(token,command);self.b.settle(token,e)
        return token,command
    def verdict(self,hit=None):
        row=dict(attempt=0,workRange=ranges.work_range('pinning',0),wholeRangeEligible=hit is None,cpuVerdict=hit)
        return dict(batchId=self.batch['batchId'],fixtureSha256='e'*64,manifestHash='f'*64,requestId=self.campaign['campaignId'],stage='pinning',parameterSha256='a'*64,rows=[row],verifiedSolution=hit,grantsRangeCredit=False)
    def publish(self,token,command,v):
        return self.j.publish(token,command,lambda raw,resource,cid:v,ranges.work_range)
    def test_credit_once_and_reopen(self):
        token,command=self.ready();v=self.verdict()
        self.assertEqual(self.publish(token,command,v),dict(stage='pinning',nextAttempt=1,coverageAdded=1))
        self.assertEqual(Journal(self.b).snapshot()['completedRanges'],1)
        with self.assertRaises(ValueError):self.publish(token,command,v)
        self.assertEqual(self.j.snapshot()['completedRanges'],1)
    def test_unknown_command_survives_reopen(self):
        token=self.register();e=self.evidence(token);self.j.claim_command(token)
        with self.assertRaises(ValueError):Journal(self.b).claim_command(token)
        self.b.settle(token,e)
        with self.assertRaisesRegex(ValueError,'proof evidence'):self.reserve()
        with self.assertRaises(ValueError):self.publish(token,str(uuid.uuid4()),self.verdict())
    def test_hit_advances_without_coverage(self):
        token,command=self.ready();hit=dict(valid=True,sequence=2147483648,locktime=500000000)
        self.assertEqual(self.publish(token,command,self.verdict(hit)),dict(stage='round1',nextAttempt=0,coverageAdded=0))
        self.batch=dict(batchId=str(uuid.uuid4()),maxAttempts=1,request=dict(stage='round1',attempt=0,manifestHash='f'*64,parameterSha256='b'*64,sequence=hit['sequence'],locktime=hit['locktime']))
        self.register()
    def test_wrong_pin_registration_rejects(self):
        token,command=self.ready();hit=dict(valid=True,sequence=2147483648,locktime=500000000)
        self.publish(token,command,self.verdict(hit))
        self.batch['request'].update(stage='round1',sequence=2147483664,locktime=500000000)
        with self.assertRaisesRegex(ValueError,'pin context'):self.register()
    def test_cleanup_required_before_verifier(self):
        token=self.register();self.evidence(token);self.j.claim_command(token);command=str(uuid.uuid4());self.j.attach_command(token,command)
        def unexpected(*args):self.fail('verifier should not run')
        with self.assertRaisesRegex(ValueError,'cleaned'):self.j.publish(token,command,unexpected,ranges.work_range)
    def test_bad_later_row_rolls_back_all_coverage(self):
        token,command=self.ready();v=self.verdict();v['rows'].append(dict(v['rows'][0],attempt=1))
        with self.assertRaisesRegex(ValueError,'noncontiguous'):self.publish(token,command,v)
        self.assertEqual(self.j.snapshot()['completedRanges'],0);self.assertEqual(self.j.snapshot()['nextAttempt'],0)
    def test_der_only_never_skips_range(self):
        token,command=self.ready();v=self.verdict(dict(valid=False,derOnly=True));v['verifiedSolution']=None
        with self.assertRaisesRegex(ValueError,'reconciliation'):self.publish(token,command,v)
        self.assertEqual(self.j.snapshot()['nextAttempt'],0)
        with self.assertRaises(ValueError):self.reserve()
    def test_wrong_fixture_or_command_rejects(self):
        token,command=self.ready();v=self.verdict()
        with self.assertRaises(ValueError):self.publish(token,str(uuid.uuid4()),v)
        for key in ('fixtureSha256','manifestHash','requestId','batchId','parameterSha256','stage'):
            with self.subTest(key=key),self.assertRaises(ValueError):self.publish(token,command,dict(v,**{key:'wrong'}))
        self.assertEqual(self.j.snapshot()['completedRanges'],0)
    def test_initialization_cannot_reset_progress(self):
        token,command=self.ready();self.publish(token,command,self.verdict())
        import sqlite3
        with self.assertRaises((sqlite3.OperationalError,ValueError)):self.j.initialize('e'*64,'f'*64,self.campaign['campaignId'])
        self.assertEqual(self.j.snapshot()['nextAttempt'],1)
    def test_launch_without_registered_batch_rejected_before_claim(self):
        token=self.reserve()
        for mode in ('prepare','arm'):self.b.claim_operation(token,mode)
        with self.assertRaisesRegex(ValueError,'registered proof'):self.b.claim_operation(token,'launch')
        self.j.register(token,json.dumps(self.batch).encode(),lambda b:b['request'])
        self.b.claim_operation(token,'launch')
        with self.assertRaisesRegex(ValueError,'before launch'):self.j.register(token,json.dumps(self.batch).encode(),lambda b:b['request'])
    def test_reconciled_capacity_rejection_allows_same_range_new_budget(self):
        token=self.register()
        for mode in ('prepare','arm','launch'):self.b.claim_operation(token,mode)
        self.b.record_capacity_rejection(token,dict(code='InsufficientInstanceCapacity',clientToken=token))
        with self.assertRaises(ValueError):self.j.close_capacity_rejection(token)
        e=dict(clientToken=token,instancesByToken=0,instancesByTag=0,volumesRemaining=0,
               securityGroupsRemaining=0,schedulesRemaining=0,functionsRemaining=0,
               rolesRemaining=0,instanceProfilesRemaining=0,receiptSha256='d'*64)
        self.b.settle_rejected(token,e);self.j.close_capacity_rejection(token)
        self.assertEqual(self.j.snapshot()['nextAttempt'],0)
        self.batch['batchId']=str(uuid.uuid4());self.register()
        self.assertEqual(self.b.snapshot()['committedMicroUsd'],4_000_000)
    def test_allocated_session_cannot_close_as_capacity_rejection(self):
        token,command=self.ready()
        with self.assertRaises(ValueError):self.j.close_capacity_rejection(token)
    def test_three_solutions_end_search_without_hit_range_credit(self):
        token,command=self.ready();pin=dict(valid=True,sequence=2147483648,locktime=500000000)
        self.publish(token,command,self.verdict(pin))
        for stage in ('round1','round2'):
            self.batch=dict(batchId=str(uuid.uuid4()),maxAttempts=1,request=dict(stage=stage,attempt=0,manifestHash='f'*64,parameterSha256='a'*64,sequence=pin['sequence'],locktime=pin['locktime']))
            token,command=self.ready();hit=dict(valid=True,indices=list(range(9)))
            v=self.verdict(hit);v['stage']=stage;v['rows'][0]['workRange']=ranges.work_range(stage,0)
            self.publish(token,command,v)
        self.assertEqual(self.j.snapshot()['stage'],'solved')
        self.assertEqual(self.j.snapshot()['completedRanges'],0)
        with self.assertRaisesRegex(ValueError,'solved'):self.reserve()
    def test_invalid_final_solution_rolls_back_prior_empty_row(self):
        token,command=self.ready();v=self.verdict()
        bad=dict(valid=True,sequence=True,locktime=500000000)
        v['rows'].append(dict(attempt=1,workRange=ranges.work_range('pinning',1),wholeRangeEligible=False,cpuVerdict=bad))
        v['verifiedSolution']=bad
        with self.assertRaisesRegex(ValueError,'invalid pin'):self.publish(token,command,v)
        self.assertEqual(self.j.snapshot()['completedRanges'],0)
        self.assertEqual(self.j.snapshot()['stage'],'pinning')
