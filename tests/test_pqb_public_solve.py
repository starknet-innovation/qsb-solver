"""The deadline cleanup must stop only its isolated queue and campaign instances."""
import importlib.util
from pathlib import Path
import unittest

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('pqb_batch_cleanup',ROOT/'ops/pqb-public-solve/cleanup.py')
cleanup=importlib.util.module_from_spec(spec);spec.loader.exec_module(cleanup)


class CleanupTests(unittest.TestCase):
    def run_step(self,queues=None,environments=None,jobs=None,instances=None):
        calls=[]
        def call(service,operation,**params):
            calls.append((service,operation,params))
            if operation=='describe-job-queues':return {'jobQueues':queues or []}
            if operation=='describe-compute-environments':return {'computeEnvironments':environments or []}
            if operation=='list-jobs':return {'jobSummaryList':[j for j in jobs or [] if j['status']==params['jobStatus']]}
            if operation=='describe-instances':return {'Reservations':[{'Instances':instances or []}]}
            return {}
        result=cleanup.stop(call,'queue-ours','environment-ours','token-ours')
        return result,calls

    def test_cancel_queued_terminate_running_and_disable(self):
        result,calls=self.run_step(queues=[{'state':'ENABLED','status':'VALID'}],
            environments=[{'state':'ENABLED','status':'VALID'}],jobs=[{'jobId':'a','status':'RUNNABLE'},{'jobId':'b','status':'RUNNING'}])
        self.assertFalse(result['done'])
        self.assertEqual([(o,p['jobId']) for _,o,p in calls if o in ('cancel-job','terminate-job')],[('cancel-job','a'),('terminate-job','b')])
        self.assertTrue(any(o=='update-compute-environment' and p['state']=='DISABLED' for _,o,p in calls))
        self.assertFalse(any(o.startswith('delete') for _,o,_ in calls))

    def test_delete_disabled_queue_with_association(self):
        result,calls=self.run_step(queues=[{'state':'DISABLED','status':'VALID','computeEnvironmentOrder':[{'order':1}]}])
        self.assertFalse(result['done'])
        self.assertTrue(any(o=='delete-job-queue' and p['jobQueue']=='queue-ours' for _,o,p in calls))
        self.assertFalse(any(o=='update-job-queue' for _,o,_ in calls))
        self.assertFalse(any(o=='delete-compute-environment' for _,o,_ in calls))

    def test_invalid_disabled_queue_is_deleted_not_waited_on(self):
        result,calls=self.run_step(queues=[{'state':'DISABLED','status':'INVALID'}],environments=[{'state':'DISABLED','status':'INVALID'}])
        self.assertEqual(result['queueDeletionPending'],True)
        self.assertTrue(any(o=='delete-job-queue' for _,o,_ in calls))

    def test_transitional_queue_is_waited_on(self):
        for status in ('CREATING','UPDATING','DELETING'):
            with self.subTest(status=status):
                result,calls=self.run_step(queues=[{'state':'DISABLED','status':status}])
                self.assertEqual(result['queueStatus'],status)
                self.assertFalse(any(o.startswith('delete') for _,o,_ in calls))

    def test_deleting_queue_does_not_delete_environment_early(self):
        result,calls=self.run_step(queues=[{'state':'DISABLED','status':'DELETING'}],environments=[{'state':'DISABLED','status':'VALID'}])
        self.assertFalse(result['done']);self.assertFalse(any(o=='delete-compute-environment' for _,o,_ in calls))

    def test_environment_is_deleted_after_queue(self):
        result,calls=self.run_step(environments=[{'state':'DISABLED','status':'VALID'}])
        self.assertFalse(result['done']);self.assertTrue(any(o=='delete-compute-environment' for _,o,_ in calls))

    def test_instance_reconciliation_is_campaign_scoped(self):
        result,calls=self.run_step(instances=[{'InstanceId':'ours','State':{'Name':'running'},'BlockDeviceMappings':[{'Ebs':{'VolumeId':'volume-ours'}}]}])
        self.assertFalse(result['done']);self.assertEqual(result['volumeIds'],['volume-ours'])
        request=next(p for _,o,p in calls if o=='describe-instances')
        self.assertEqual(request['Filters'],[{'Name':'tag:QsbSolveCampaign','Values':['token-ours']}])
        self.assertEqual(next(p for _,o,p in calls if o=='terminate-instances')['InstanceIds'],['ours'])

    def test_complete_only_after_instance_termination(self):
        result,_=self.run_step(instances=[{'InstanceId':'ours','State':{'Name':'terminated'}}])
        self.assertTrue(result['done'])


if __name__=='__main__':unittest.main()
