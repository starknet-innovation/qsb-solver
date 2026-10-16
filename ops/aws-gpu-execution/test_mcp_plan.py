import copy
import importlib.util
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import mcp_plan as p

CONFIG = dict(account='123456789012', profile='dummy', region='eu-west-1', ami='ami-12345678901234567',
              subnet='subnet-12345678', vpc='vpc-12345678')
TOKEN='00000000-0000-4000-8000-000000000001'


def prepared():
    s=p.prepare(CONFIG, 'a'*40, {'Account':CONFIG['account']}, TOKEN)
    rs=[{'success':True,'operation':c['operation'],'requestSha256':p.request_hash(c),'result':{}} for c in s['calls']]
    rs[4]['result']['GroupId']='sg-12345678'
    return p.bind_prepared(s,rs)


def armed():
    return p.arm(prepared(),1000)


def evidence(s):
    return {'caller':{'Account':CONFIG['account']}, 'observedAt':1010,
        'lambda':{'State':'Active','CodeSha256':s['cleanupCodeSha256'],'FunctionArn':s['functionArn'],
            'Runtime':'python3.12','Handler':'cleanup.handler','Timeout':60,
            'Role':f"arn:aws:iam::{CONFIG['account']}:role/{s['name']}-cleanup",
            'Environment':{'Variables':{'RUN_TOKEN':TOKEN,'DEADLINE':str(s['deadline'])}}},
        'schedule':s['schedule'], 'quota':{'Quota':{'Value':4}},
        'instances':{'Reservations':[]}, 'activeGpus':{'Reservations':[]},
        'images':{'Images':[{'ImageId':CONFIG['ami'],'OwnerId':'898082745236','Architecture':'x86_64',
            'RootDeviceType':'ebs','RootDeviceName':'/dev/sda1','BlockDeviceMappings':[{'DeviceName':'/dev/sda1','Ebs':{}},{'DeviceName':'/dev/sdb','VirtualName':'ephemeral0'}]}]},
        'groups':{'SecurityGroups':[{'GroupId':'sg-12345678','VpcId':CONFIG['vpc'],'IpPermissions':[]}]}}


class PlannerTests(unittest.TestCase):
    def test_prepare_is_only_exact_scoped_requests(self):
        s=prepared()
        self.assertEqual(9,len(s['calls']))
        doc=json.loads(s['calls'][6]['parameters']['PolicyDocument'])
        self.assertEqual(TOKEN,doc['Statement'][1]['Condition']['StringEquals']['ec2:ResourceTag/QsbBenchmarkToken'])
        self.assertNotIn('RunInstances',str(s['calls']))

    def test_prepare_rejects_wrong_account(self):
        with self.assertRaises(ValueError):p.prepare(CONFIG,'a'*40,{'Account':'999'})

    def test_prepare_missing_receipt_rejects(self):
        s=p.prepare(CONFIG,'a'*40,{'Account':CONFIG['account']},TOKEN)
        with self.assertRaises(ValueError):p.bind_prepared(s,[])

    def test_arm_same_fixed_deadline(self):
        s=armed()
        self.assertEqual(2500,s['deadline'])
        self.assertEqual('at(1970-01-01T00:42:00)',s['schedule']['ScheduleExpression'])
        with self.assertRaises(ValueError):p.arm(s,2000)

    def test_launch_exact_guarded_request(self):
        s=armed();p.launch(s,evidence(s),1010)
        r=s['calls'][0]['parameters']
        self.assertEqual('launch-intent',s['phase'])
        self.assertEqual(TOKEN,r['ClientToken'])
        self.assertEqual('terminate',r['InstanceInitiatedShutdownBehavior'])
        self.assertEqual(1,r['MaxCount'])
        self.assertIn('2500',r['UserData'])
        self.assertTrue(r['BlockDeviceMappings'][0]['Ebs']['DeleteOnTermination'])
        with self.assertRaises(ValueError):p.launch(s,evidence(s),1011)

    def test_stale_or_future_observation_rejects(self):
        for timestamp in [900,1011]:
            s=armed();e=evidence(s);e['observedAt']=timestamp
            with self.assertRaises(ValueError):p.launch(s,e,1010)

    def test_early_expiry_rejects(self):
        s=armed()
        with self.assertRaises(ValueError):p.launch(s,evidence(s),1301)

    def test_readback_mismatch_rejects(self):
        for key,value in [('State','Pending'),('CodeSha256','bad'),('Timeout',61),('Role','wrong')]:
            s=armed();e=evidence(s);e['lambda'][key]=value
            with self.subTest(key=key),self.assertRaises(ValueError):p.launch(s,e,1010)

    def test_schedule_mutation_rejects(self):
        s=armed();e=copy.deepcopy(evidence(s));e['schedule']['Target']['Input']='{"other":1}'
        with self.assertRaises(ValueError):p.launch(s,e,1010)

    def test_existing_or_other_capacity_rejects(self):
        for key in ['instances','activeGpus']:
            s=armed();e=evidence(s);e[key]['Reservations']=[{}]
            with self.subTest(key=key),self.assertRaises(ValueError):p.launch(s,e,1010)

    def test_ami_group_and_quota_rejects(self):
        for kind in ['ami','group','quota']:
            s=armed();e=evidence(s)
            if kind=='ami':e['images']['Images'][0]['OwnerId']='other'
            if kind=='group':e['groups']['SecurityGroups'][0]['IpPermissions']=[{}]
            if kind=='quota':e['quota']['Quota']['Value']=0
            with self.subTest(kind=kind),self.assertRaises(ValueError):p.launch(s,e,1010)

    def test_receipt_wrong_request_binding_rejects(self):
        for field,value in [('success',False),('operation','DeleteRole'),('requestSha256','wrong')]:
            s=p.prepare(CONFIG,'a'*40,{'Account':CONFIG['account']},TOKEN)
            receipts=[{'success':True,'operation':c['operation'],'requestSha256':p.request_hash(c),'result':{}} for c in s['calls']]
            receipts[4]['result']['GroupId']='sg-12345678'
            receipts[0][field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):p.bind_prepared(s,receipts)

    def test_extra_ebs_mapping_rejects(self):
        s=armed();e=evidence(s)
        e['images']['Images'][0]['BlockDeviceMappings'].append({'DeviceName':'/dev/sdf','Ebs':{}})
        with self.assertRaises(ValueError):p.launch(s,e,1010)

    def test_cleanup_reads_detached_volume_and_never_claims_complete(self):
        s=armed();s['volumeIds']=['vol-12345678']
        calls=p.cleanup_inventory(s)
        self.assertTrue(any(c['operation']=='DescribeVolumes' for c in calls))
        self.assertTrue(all(c['operation'].startswith(('Get','List','Describe')) for c in calls))
        self.assertEqual('arm-intent',s['phase'])

if __name__=='__main__':unittest.main()
