import copy
import sys
from pathlib import Path
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parent))
import fresh_campaign as f
from test_mcp_plan import CONFIG, evidence as cloud_evidence


def quote():
    return dict(computeUsdPerHour='1.123',publicIpv4UsdPerHour='0.005',gp3UsdPerGiBMonth='0.088',
                fixedControlNetworkReserveUsd='2',observedAt=1000,sourceEvidenceSha256='a'*64)


def prepared():
    s=f.prepare(CONFIG,'b'*40,dict(caller={'Account':CONFIG['account']},quote=quote(),
                  priorGpuCleanupVerified=True,priorCleanupReceiptSha256='c'*64),1000)
    receipts=[dict(success=True,operation=c['operation'],requestSha256=f.base.request_hash(c),result={}) for c in s['calls']]
    receipts[4]['result']['GroupId']='sg-12345678'
    return f.base.bind_prepared(s,receipts)


def evidence(s):
    e=cloud_evidence(s);e['lambda']['Environment']['Variables']['RUN_TOKEN']=s['token']
    return e


class FreshCampaignTests(unittest.TestCase):
    def test_all_in_quote_reserves_full_gpu_budget(self):
        b=f.reserve(quote(),1000)
        self.assertEqual(b['aggregateGpuHoursCap'],24)
        self.assertLess(f.Decimal(b['reservedUsd']),f.Decimal(30))
        self.assertGreater(f.Decimal(b['reservedUsd']),f.Decimal(29))
        self.assertEqual(b['rootGiB'],80)

    def test_expensive_missing_nonfinite_and_stale_quotes_reject(self):
        for key,value in [('computeUsdPerHour','2'),('computeUsdPerHour','NaN'),('publicIpv4UsdPerHour','0'),
                          ('gp3UsdPerGiBMonth','0'),('fixedControlNetworkReserveUsd','1'),('observedAt',-90000)]:
            q=quote();q[key]=value
            with self.subTest(key=key,value=value),self.assertRaises(ValueError):f.reserve(q,1000)

    def test_old_cleanup_not_confirmed_rejects(self):
        with self.assertRaises(ValueError):f.prepare(CONFIG,'b'*40,{'priorGpuCleanupVerified':False},1000)

    def test_fixed_compute_termination_and_budget_deadlines(self):
        s=f.arm(prepared(),1000)
        self.assertEqual(s['computeDeadline'],1000+23*3600)
        self.assertEqual(s['deadline'],1000+23*3600+15*60)
        self.assertEqual(s['gpuBudgetExpiresAt'],1000+24*3600)
        self.assertEqual(s['calls'][0]['parameters']['Environment']['Variables']['DEADLINE'],str(s['deadline']))
        self.assertEqual(s['calls'][1]['parameters'],s['schedule'])
        with self.assertRaises(ValueError):f.arm(s,1100)

    def test_launch_uses_same_fixed_deadline_and_single_intent(self):
        s=f.arm(prepared(),1000);f.launch(s,evidence(s),1010)
        request=s['calls'][0]['parameters']
        self.assertNotIn('/sbin/shutdown -h +55\n',request['UserData'])
        self.assertIn('/sbin/shutdown -h +1380\n',request['UserData'])
        self.assertIn(str(s['computeDeadline']),request['UserData'])
        self.assertEqual(request['MinCount'],request['MaxCount'])
        self.assertEqual(request['MaxCount'],1)
        with self.assertRaises(ValueError):f.launch(s,evidence(s),1011)

    def test_launch_late_or_modified_deadline_rejects(self):
        s=f.arm(prepared(),1000)
        with self.assertRaises(ValueError):f.launch(s,evidence(s),1301)
        for field in ['deadline','computeDeadline','gpuBudgetExpiresAt']:
            changed=copy.deepcopy(s);changed[field]+=60
            with self.subTest(field=field),self.assertRaises(ValueError):f.launch(changed,evidence(changed),1010)

    def test_historical_campaign_forbidden(self):
        s=prepared();s.pop('campaignType')
        with self.assertRaises(ValueError):f.arm(s,1000)


if __name__=='__main__':unittest.main()
