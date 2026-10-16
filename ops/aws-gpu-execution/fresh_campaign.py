"""One-shot public-fixture campaign planner; no AWS calls or automatic retries.

Reservations use explicit quoted tariffs, not an assertion about the final bill.
The sole host stops compute at 23h and is terminated at 23h15 after arming.
The remaining 45 minutes are reserved for control-plane termination delay.
"""
import argparse
from datetime import datetime, timedelta, timezone
from decimal import Decimal, InvalidOperation
import fcntl
import hashlib
import json
import math
from pathlib import Path
import subprocess

import mcp_plan as base

GPU_HOURS = 24
USD_CAP = Decimal('30')
COMPUTE_SECONDS = 23*3600
TERMINATE_SECONDS = 23*3600+15*60
REQUIRED_QUOTE_KEYS = {'computeUsdPerHour','publicIpv4UsdPerHour','gp3UsdPerGiBMonth',
                       'fixedControlNetworkReserveUsd','observedAt','sourceEvidenceSha256'}


def decimal(value):
    base.require(isinstance(value,str), 'Quoted rates must be decimal strings')
    try:
        amount = Decimal(value)
    except InvalidOperation as exc:
        raise ValueError('Invalid quoted rate') from exc
    base.require(amount.is_finite() and amount >= 0, 'Invalid quoted rate')
    return amount


def reserve(quote, now):
    base.require(set(quote) == REQUIRED_QUOTE_KEYS, 'Unexpected quote inventory')
    base.require(type(quote['observedAt']) is int and 0 <= now-quote['observedAt'] <= 86400,
                 'Fresh price evidence required')
    digest=quote['sourceEvidenceSha256']
    base.require(isinstance(digest,str) and len(digest)==64 and all(c in '0123456789abcdef' for c in digest),
                 'Price evidence hash required')
    compute=decimal(quote['computeUsdPerHour'])
    ip=decimal(quote['publicIpv4UsdPerHour'])
    disk=decimal(quote['gp3UsdPerGiBMonth'])*80/720
    fixed=decimal(quote['fixedControlNetworkReserveUsd'])
    base.require(compute > 0 and ip >= Decimal('0.005') and disk > 0 and fixed >= 2,
                 'Compute, IP, EBS and control/network reserves required')
    total=(compute+ip+disk)*GPU_HOURS+fixed
    base.require(total <= USD_CAP, 'All-in reservation exceeds authorized USD cap')
    return dict(aggregateGpuHoursCap=GPU_HOURS, usdCap=str(USD_CAP), rootGiB=80,
                reservedUsd=str(total), hourlyComputeUsd=str(compute), hourlyIpUsd=str(ip),
                hourlyEbsUsd=str(disk), fixedControlNetworkReserveUsd=str(fixed), quote=quote,
                assumptions='One g5.xlarge,80GiB gp3 defaultIOPS/throughput,one publicIPv4,720hour month; quoted tariffs exclude billing deviations; reserve is not final invoice')


def prepare(config, commit, evidence, now):
    base.require(evidence.get('priorGpuCleanupVerified') is True, 'Prior GPU cleanup must be independently verified')
    cleanup=evidence.get('priorCleanupReceiptSha256','')
    base.require(len(cleanup)==64 and all(c in '0123456789abcdef' for c in cleanup), 'Prior cleanup receipt hash required')
    budget=reserve(evidence['quote'],now)
    state=base.prepare(config,commit,evidence['caller'])
    state.update(campaignType='corrected-fresh-public-proof-v1', budget=budget,
                 priorCleanupReceiptSha256=cleanup, paidLaunchCountLimit=1,
                 coveredGpuHoursBeforeThisCampaign=0, coveragePolicy='No retry or replacement; uncertain submissions and incomplete ranges remain uncredited')
    return state


def arm(state, now):
    base.require(state.get('campaignType')=='corrected-fresh-public-proof-v1', 'Wrong campaign; historical state forbidden')
    # Recheck quotation and cap before any future paid launch is possible.
    base.require(reserve(state['budget']['quote'],now)==state['budget'], 'Budget changed')
    base.arm(state,now)
    deadline=now+TERMINATE_SECONDS
    state.update(armedAt=now, deadline=deadline, computeDeadline=now+COMPUTE_SECONDS,
                 gpuBudgetExpiresAt=now+GPU_HOURS*3600)
    state['calls'][0]['parameters']['Environment']['Variables']['DEADLINE']=str(deadline)
    expression=datetime.fromtimestamp(deadline,timezone.utc).replace(second=0)+timedelta(minutes=1)
    state['schedule']['ScheduleExpression']=f'at({expression:%Y-%m-%dT%H:%M:%S})'
    state['calls'][1]['parameters']=state['schedule']
    state['transportNotes'].append('No extension/rearm/replacement. Search controller must stop dispatch and checkpoint at computeDeadline. Host stops at computeDeadline and independent Scheduler terminates at deadline; reconcile actual termination before budget expiry.')
    return state


def launch(state,evidence,now):
    base.require(state.get('campaignType')=='corrected-fresh-public-proof-v1', 'Wrong campaign')
    base.require(state['paidLaunchCountLimit']==1 and state['coveredGpuHoursBeforeThisCampaign']==0, 'One fresh GPU only')
    base.require(0 <= now-state['armedAt'] <= 300, 'Launch window expired; never rearm')
    base.require(state['computeDeadline']==state['armedAt']+COMPUTE_SECONDS and
                 state['deadline']==state['armedAt']+TERMINATE_SECONDS and
                 state['gpuBudgetExpiresAt']==state['armedAt']+GPU_HOURS*3600, 'Fixed deadlines changed')
    base.require(reserve(state['budget']['quote'],now)==state['budget'], 'Budget changed')
    base.launch(state,evidence,now)
    request=state['calls'][0]['parameters']
    # The historical helper has an initial +55 fallback; replace only that line.
    boot=base.boot_script(datetime.fromtimestamp(state['computeDeadline'],timezone.utc)-timedelta(minutes=55))
    anchor='/sbin/shutdown -h +55\n'
    base.require(boot.count(anchor)==1, 'Boot fallback anchor changed')
    minutes=math.ceil((state['computeDeadline']-now)/60)
    request['UserData']=boot.replace(anchor,f'/sbin/shutdown -h +{minutes}\n')
    state['paidLaunchReserved']=True
    return state


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('phase',choices=['prepare','prepared','arm','launch','cleanup-inventory'])
    parser.add_argument('--state',type=Path,required=True)
    parser.add_argument('--evidence',type=Path)
    args=parser.parse_args()
    base.require(base.ROOT not in args.state.resolve().parents,'State must be outside checkout')
    args.state.parent.mkdir(parents=True,exist_ok=True)
    with args.state.with_suffix(args.state.suffix+'.lock').open('a') as lock:
        fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
        config=base.load_config()
        base.require(not subprocess.check_output(['git','status','--porcelain'],cwd=base.ROOT),'Dirty checkout')
        commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=base.ROOT,text=True).strip()
        base.require(commit==subprocess.check_output(['git','rev-parse','@{upstream}'],cwd=base.ROOT,text=True).strip(),'Source not pushed')
        evidence=json.loads(args.evidence.read_text()) if args.evidence else None
        now=base.epoch_now()
        if args.phase=='prepare':
            state=prepare(config,commit,evidence,now)
            with args.state.open('x') as stream:
                json.dump(state,stream,indent=2);stream.flush()
                import os
                os.fsync(stream.fileno())
        else:
            state=json.loads(args.state.read_text())
            base.require(state['operatorConfig']==config and state['controllerCommit']==commit,'Source or scope changed')
            base.require(state.get('campaignType')=='corrected-fresh-public-proof-v1','Historical state forbidden')
            if args.phase=='cleanup-inventory':
                print(json.dumps(base.cleanup_inventory(state),indent=2));return
            if args.phase=='prepared':state=base.bind_prepared(state,evidence)
            elif args.phase=='arm':state=arm(state,now)
            elif args.phase=='launch':state=launch(state,evidence,now)
            temporary=args.state.with_suffix('.tmp')
            with temporary.open('w') as stream:
                json.dump(state,stream,indent=2);stream.flush()
                import os
                os.fsync(stream.fileno())
            temporary.replace(args.state)
        print(json.dumps(state,indent=2))


if __name__=='__main__':main()
