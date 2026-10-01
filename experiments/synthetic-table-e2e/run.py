"""Fixed public-table subprocess benchmark. No solver, transactions or search."""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import signal
import selectors
import statistics
import subprocess
import time

EXPECTED_TABLE = '6c6af155b84552c23ee2fc17b29dfe31bad768b92ca43e3198efc7a0e097ad8f'
COMPLETE = 'Synthetic public table subprocess completed; receipt saved.'
REPETITIONS = (1, 4, 16)
PAIRS = 7
SCOPE = 'fresh process through durable child report and parent validation; excludes runner journal fsync and cloud setup'
KERNEL = 'e5ef86cb59945d71acc48fc43299c4f176c41b25a4141b813f2c59a78e246d79'

def require(ok, message):
    if not ok: raise ValueError(message)

def strict_json(raw):
    def pairs(items):
        out = {}
        for key, value in items:
            require(key not in out, 'duplicate JSON key')
            out[key] = value
        return out
    def invalid(value): raise ValueError('nonfinite JSON value')
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid)

def positive(value):
    return type(value) in (int, float) and math.isfinite(value) and value > 0

def save(path, value):
    temporary = path.with_suffix('.tmp')
    with temporary.open('w') as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.flush(); os.fsync(stream.fileno())
    os.replace(temporary, path)
    fd = os.open(path.parent, os.O_RDONLY)
    try: os.fsync(fd)
    finally: os.close(fd)

def execute(command, deadline, log):
    remaining = min(90, deadline - time.monotonic())
    require(remaining > 0, 'aggregate deadline expired')
    start = time.monotonic()
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    output = bytearray()
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    try:
        while selector.get_map():
            left = start + remaining - time.monotonic()
            if left <= 0: raise subprocess.TimeoutExpired(command, remaining)
            for key, _ in selector.select(left):
                chunk = os.read(key.fileobj.fileno(), 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                space = 1_000_000 - len(output)
                output.extend(chunk[:space])
                require(len(chunk) <= space, 'child log too large')
        process.wait(timeout=max(0.001, start + remaining - time.monotonic()))
    except BaseException:
        try: os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError: pass
        process.wait()
        with log.open('xb') as stream: stream.write(output)
        raise
    finally:
        selector.close()
        process.stdout.close()
    seconds = time.monotonic() - start
    with log.open('xb') as stream: stream.write(output)
    code=process.returncode
    require(code == 0, 'child failed; see ' + log.name)
    require(log.read_text().count(COMPLETE)==1, 'missing or ambiguous completion')
    return seconds

def check_report(row, arm, repetitions):
    require(row.get('status') == 'passed', 'report not passed')
    require(row.get('arm') == arm, 'arm mismatch')
    require(type(row.get('repetitions')) is int and row['repetitions'] == repetitions, 'repetition mismatch')
    require(row.get('table_sha256') == EXPECTED_TABLE, 'unexpected public table hash')
    require(row.get('gpu') == 'NVIDIA A10G', 'wrong GPU')
    for key, wanted in {'schema':1,'public_scalar':1,'geometry':15,'records_per_table':1048576,'openssl_samples_per_table':252}.items():
        require(type(row.get(key)) is int and row[key] == wanted, 'wrong '+key)
    require(row.get('expected_table_sha256') == EXPECTED_TABLE and row.get('original_kernel_sha256') == KERNEL, 'identity mismatch')
    tables=row.get('tables'); require(type(tables) is list and len(tables)==repetitions, 'missing tables')
    phases=('ladder_ms','allocate_ms','upload_ms','kernel_wall_ms','download_ms','verification_ms','cleanup_ms')
    for index, table in enumerate(tables):
        require(type(table.get('index')) is int and table['index']==index, 'wrong table order')
        require(table.get('table_sha256')==EXPECTED_TABLE, 'table hash mismatch')
        for key in (*phases,'hash_ms','kernel_ms','construction_ms'):
            value=table.get(key); require(type(value) in (int,float) and math.isfinite(value) and value>=0, 'invalid phase '+key)
        require(table['kernel_ms']>0, 'invalid event timing')
        require(table['construction_ms']>0 and abs(sum(table[k] for k in phases)-table['construction_ms'])<=0.00001, 'construction partition mismatch')
    for key in ('context_init_ms','output_allocation_ms','output_cleanup_ms','before_report_elapsed_ms'):
        value=row.get(key); require(type(value) in (int,float) and math.isfinite(value) and value>=0, 'invalid phase '+key)
    accounted=sum(row[k] for k in ('context_init_ms','output_allocation_ms','output_cleanup_ms'))+sum(t['construction_ms']+t['hash_ms'] for t in tables)
    require(row['before_report_elapsed_ms']+0.0001>=accounted, 'whole interval shorter than phases')
    require(row.get('noSolverSearch') is True, 'scope mismatch')

def summarize(result):
    require(result.get('status') == 'passed', 'incomplete run')
    checks=result.get('sanitizers',[])
    require([(r['tool'],r['arm']) for r in checks]==[(t,a) for t in ('memcheck','racecheck','synccheck') for a in ('baseline','candidate')], 'missing sanitizer prerequisites')
    for row in checks:
        require(positive(row['seconds']), 'invalid sanitizer time')
        check_report(row['report'],row['arm'],1)
    expected = [(n, pair, arm) for n in REPETITIONS for pair in range(PAIRS)
                for arm in (('baseline','candidate') if pair % 2 == 0 else ('candidate','baseline'))]
    samples = result['samples']
    require([(r['repetitions'],r['pair'],r['arm']) for r in samples] == expected, 'missing or reordered samples')
    output = {}
    for sample in samples:
        require(type(sample['pair']) is int and type(sample['repetitions']) is int, 'invalid sample index')
        require(positive(sample['processSeconds']) and positive(sample['pipelineSeconds']), 'invalid wall timing')
        require(sample['pipelineSeconds'] >= sample['processSeconds'], 'pipeline shorter than subprocess')
        check_report(sample['report'],sample['arm'],sample['repetitions'])
        require(sample['processSeconds']*1000+0.1 >= sample['report']['before_report_elapsed_ms'], 'external time shorter than child interval')
    for n in REPETITIONS:
        rows = [r for r in samples if r['repetitions'] == n]
        ratios = []
        for pair in range(PAIRS):
            arms = {r['arm']:r for r in rows if r['pair'] == pair}
            ratio=arms['candidate']['pipelineSeconds']/arms['baseline']['pipelineSeconds']
            require(positive(ratio), 'invalid derived ratio');ratios.append(ratio)
        output[str(n)] = {'pairedCandidateOverBaseline':ratios, 'medianRatio':statistics.median(ratios),
            'minimumRatio':min(ratios),'maximumRatio':max(ratios),
            'medianTablesPerSecond':{arm:statistics.median(n/r['pipelineSeconds'] for r in rows if r['arm']==arm) for arm in ('baseline','candidate')}}
    require(all(positive(value) for row in output.values() for value in row['medianTablesPerSecond'].values()), 'invalid throughput')
    return output

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('binary',type=Path); parser.add_argument('output',type=Path)
    args=parser.parse_args(); binary=args.binary.resolve(); root=args.output.resolve()
    require(root.is_dir(), 'output directory must exist')
    result_path=root/'result.json'; require(not result_path.exists(), 'existing run')
    result={'status':'running','binarySha256':hashlib.sha256(binary.read_bytes()).hexdigest(),
            'noSolverSearch':True,'solverThroughputMeasured':False,'measurementScope':SCOPE,'sanitizers':[],'samples':[]}
    save(result_path,result); deadline=time.monotonic()+570
    try:
        # All six sanitizer checks precede any retained performance samples.
        for tool in ('memcheck','racecheck','synccheck'):
            for arm in ('baseline','candidate'):
                stem=tool+'-'+arm; report=root/(stem+'.json'); log=root/(stem+'.log')
                seconds=execute(['compute-sanitizer','--tool',tool,'--error-exitcode','42',str(binary),str(report),arm,'1'],deadline,log)
                row=strict_json(report.read_text());check_report(row,arm,1)
                text=log.read_text()
                wanted='========= RACECHECK SUMMARY: 0 hazards displayed (0 errors, 0 warnings)' if tool=='racecheck' else '========= ERROR SUMMARY: 0 errors'
                require('COMPUTE-SANITIZER' in text and [x.strip() for x in text.splitlines() if 'SUMMARY:' in x]==[wanted], 'unclean sanitizer')
                result['sanitizers'].append({'tool':tool,'arm':arm,'seconds':seconds,'report':row,'logSha256':hashlib.sha256(log.read_bytes()).hexdigest()});save(result_path,result)
        for n in REPETITIONS:
            for pair in range(PAIRS):
                for arm in (('baseline','candidate') if pair%2==0 else ('candidate','baseline')):
                    stem=f'sample-{n}-{pair}-{arm}'; report=root/(stem+'.json'); log=root/(stem+'.log')
                    start=time.monotonic()
                    seconds=execute([str(binary),str(report),arm,str(n)],deadline,log)
                    row=strict_json(report.read_text());check_report(row,arm,n)
                    total=time.monotonic()-start
                    result['samples'].append({'repetitions':n,'pair':pair,'arm':arm,'processSeconds':seconds,'pipelineSeconds':total,'report':row});save(result_path,result)
        result['status']='passed';result['summary']=summarize(result);save(result_path,result)
    except BaseException as error:
        result['status']='failed';result['error']=str(error);save(result_path,result);raise

if __name__ == '__main__': main()
