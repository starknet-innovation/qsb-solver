"""Review regressions: local files, local Git remotes and mocked APIs only."""
import contextlib
import copy
import gzip
import importlib.util
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
sys.path.insert(0,str(ROOT/'ops/aws-gpu-execution'))
from source_identity import pushed_commit
from pqb_import import verify_runtime, import_image
from check_pqb_final import native_rows, reviewed_gate
from pqb_descriptor import sha


def controller(path):
    spec=importlib.util.spec_from_file_location('review_controller',ROOT/path)
    module=importlib.util.module_from_spec(spec)
    with mock.patch.dict(sys.modules),mock.patch.object(sys,'path',[str((ROOT/path).parent),*sys.path]):
        sys.modules.pop('cleanup',None)
        spec.loader.exec_module(module)
    return module


class DurableStateTests(unittest.TestCase):
    def test_both_controllers_sync_file_then_rename_then_directory(self):
        for source in ('ops/pqb-public-solve/control.py','ops/aws-gpu-execution/control.py'):
            mod=controller(source)
            with self.subTest(source=source),tempfile.TemporaryDirectory() as temp:
                path=Path(temp)/'state.json';events=[]
                real_sync,real_replace=os.fsync,Path.replace
                def sync(fd):
                    events.append('directory-sync' if stat.S_ISDIR(os.fstat(fd).st_mode) else 'file-sync')
                    real_sync(fd)
                def replace(src,dst):
                    self.assertEqual(json.loads(src.read_text()),{'phase':'arming'})
                    events.append('rename');return real_replace(src,dst)
                with mock.patch.object(mod.os,'fsync',sync),mock.patch.object(Path,'replace',replace):
                    mod.save(path,{'phase':'arming'})
                    events.append('mutation-dispatch')
                self.assertEqual(events,['file-sync','rename','directory-sync','mutation-dispatch'])

    def test_failed_sync_cannot_acknowledge_state_before_a_mutation(self):
        for source in ('ops/pqb-public-solve/control.py','ops/aws-gpu-execution/control.py'):
            mod=controller(source)
            for fail_at in (1,2):
                with self.subTest(source=source,fail_at=fail_at),tempfile.TemporaryDirectory() as temp:
                    count=0;dispatched=[];real_sync=os.fsync
                    def sync(fd):
                        nonlocal count
                        count+=1
                        if count==fail_at:raise OSError('simulated storage failure')
                        real_sync(fd)
                    with mock.patch.object(mod.os,'fsync',sync),self.assertRaises(OSError):
                        mod.save(Path(temp)/'state.json',{'phase':'arming'})
                        dispatched.append(True)
                    self.assertEqual(dispatched,[])


class LiveRemoteTests(unittest.TestCase):
    def test_stale_tracking_ref_cannot_authorize_a_controller(self):
        with tempfile.TemporaryDirectory() as temp:
            remote=Path(temp)/'remote.git';repo=Path(temp)/'controller'
            def run(*args,cwd=None):
                return subprocess.check_output(['git',*args],cwd=cwd,text=True,stderr=subprocess.DEVNULL).strip()
            run('init','--bare',str(remote));run('init',str(repo))
            run('config','user.name','Public Test',cwd=repo);run('config','user.email','public@example.invalid',cwd=repo)
            (repo/'source').write_text('public synthetic controller')
            run('add','source',cwd=repo);run('commit','-m','initial',cwd=repo)
            run('remote','add','origin',str(remote),cwd=repo)
            run('push','-u','origin','HEAD:refs/heads/controller',cwd=repo)
            head=run('rev-parse','HEAD',cwd=repo)
            self.assertEqual(pushed_commit(repo),head)
            # The local tracking ref still says HEAD, but the live remote moved.
            other=run('commit-tree','HEAD^{tree}','-p','HEAD','-m','remote replacement',cwd=repo)
            run('push','origin',other+':refs/heads/other',cwd=repo)
            run('--git-dir='+str(remote),'update-ref','refs/heads/controller',other)
            self.assertEqual(run('rev-parse','@{upstream}',cwd=repo),head)
            with self.assertRaisesRegex(ValueError,'live pushed'):pushed_commit(repo)
            run('--git-dir='+str(remote),'update-ref','-d','refs/heads/controller')
            with self.assertRaises(subprocess.CalledProcessError):pushed_commit(repo)


class CleanupPaginationTests(unittest.TestCase):
    def run_cleanup(self,fail=False):
        mod=controller('ops/aws-gpu-execution/control.py')
        with tempfile.TemporaryDirectory() as temp:
            config=dict(account='123456789012',region='eu-west-1',profile='test',ami='ami-test',subnet='subnet-test',vpc='vpc-test')
            path=Path(temp)/'state.json';name='qsb-bench-test';commit='a'*40
            path.write_text(json.dumps(dict(name=name,token='public-test-token',phase='prepared',
                controllerCommit=commit,operatorConfig=config,securityGroup='sg-test')))
            calls=[]
            def call(service,operation,**params):
                calls.append((service,operation,params))
                if service=='sts':return {'Account':config['account']}
                if operation=='describe-instances':return {'Reservations':[]}
                if operation=='list-schedules':return {'Schedules':[]}
                if operation=='list-functions':
                    if not params:return {'Functions':[{'FunctionName':f'other-{i}'} for i in range(50)],'NextMarker':'second'}
                    self.assertEqual(params,{'Marker':'second'})
                    if fail:raise RuntimeError('uncertain page read')
                    return {'Functions':[{'FunctionName':name}]}
                return {}
            with mock.patch.object(mod,'aws',call),mock.patch.object(mod,'load_config',lambda:config), \
                 mock.patch.object(mod,'pushed_commit',lambda _:commit), \
                 mock.patch.object(sys,'argv',['control.py','cleanup','--state',str(path)]),contextlib.redirect_stdout(io.StringIO()):
                if fail:
                    with self.assertRaisesRegex(RuntimeError,'uncertain'):mod.main()
                else:mod.main()
            state=json.loads(path.read_text())
            self.assertEqual(state['phase'],'prepared' if fail else 'cleaned')
            return calls

    def test_cleanup_finds_later_page_before_deleting_control_resources(self):
        calls=self.run_cleanup()
        deletion=next(i for i,c in enumerate(calls) if c[1]=='delete-function')
        page=next(i for i,c in enumerate(calls) if c[1]=='list-functions' and c[2].get('Marker')=='second')
        self.assertLess(page,deletion)

    def test_unknown_page_never_records_cleanup_or_deletes_iam(self):
        calls=self.run_cleanup(fail=True)
        self.assertFalse(any(c[0]=='iam' or c[1]=='delete-security-group' for c in calls))


class RuntimeDefaultsTests(unittest.TestCase):
    def test_omitted_runtime_fields_must_be_defaults(self):
        root=ROOT/'docs/pqb/evidence/final-image-2026-11-12/build'
        config=json.loads((root/'image-config.json').read_bytes())
        image=json.loads((root/'image.json').read_bytes())[0]
        verify_runtime(image,config)
        for key,value in [('User','attacker'),('Volumes',{'/opt/qsb-pqb':{}}),
                          ('Healthcheck',{'Test':['CMD','unexpected']}),('Shell',['/bin/unexpected']),
                          ('StopSignal','SIGKILL'),('ExposedPorts',{'9000/tcp':{}}),('UnreviewedRuntimeFlag',True)]:
            changed=copy.deepcopy(image);changed['Config'][key]=value
            with self.subTest(field=key),self.assertRaisesRegex(ValueError,key):verify_runtime(changed,config)

    def test_import_tags_inspected_immutable_id_not_a_mutable_loaded_name(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'gate').mkdir();out=root/'result';out.mkdir()
            identity=dict(imageDigest='sha256:'+'a'*64,platformDigest='sha256:'+'b'*64,configDigest='sha256:'+'c'*64)
            config=dict(architecture='amd64',os='linux',rootfs={'diff_ids':['layer']},
                        config={'WorkingDir':'/opt/qsb-pqb','Cmd':['python3','aws_entrypoint.py']})
            image=dict(Id=identity['platformDigest'],Architecture='amd64',Os='linux',RootFS={'Layers':['layer']},Config=config['config'])
            (root/'gate/oci-identity.json').write_text(json.dumps(identity));(root/'image-config.json').write_text(json.dumps(config))
            calls=[]
            def call(args,**kwargs):
                calls.append(args)
                return subprocess.CompletedProcess(args,0,'Loaded image: mutable:tag\n' if args[1]=='load' else json.dumps([image]),'')
            import_image(root,out,call)
            self.assertIn(['docker','tag',image['Id'],'qsb-pqb:final'],calls)
            self.assertNotIn(['docker','tag','mutable:tag','qsb-pqb:final'],calls)


class NativeGateTests(unittest.TestCase):
    def inputs(self):
        root=ROOT/'docs/pqb/evidence/final-image-2026-11-12'
        manifest=json.loads((root/'manifest.json').read_bytes())
        solver=json.loads((root/'release/descriptor-proposal.json').read_bytes())['solver']
        build={k:json.loads((root/'build'/n).read_bytes()) for k,n in
               [('identity','oci-identity.json'),('config','image-config.json'),('binding','binding.json'),('receipt','build-receipt.json')]}
        build['assetHashes']={n:sha((root/'build'/n).read_bytes()) for n in ('binding.json','oci-identity.json')}
        checksums=(root/'verification/native-gate-SHA256SUMS').read_bytes()
        gate=reviewed_gate(checksums,manifest['nativeQualificationHarnessCommit'],solver,build)
        files=json.loads(gzip.decompress((root/'native/public-result.json.gz').read_bytes()))
        return solver,build,gate,files,checksums,manifest

    def test_altered_gate_cannot_claim_reviewed_correctness(self):
        solver,build,gate,files,checksums,manifest=self.inputs()
        changed=checksums.replace(b'e243614b3ec20c4ad9545a37b3536a762f34d8273ce2025f1fb33672afa01af3',b'0'*64)
        with self.assertRaisesRegex(ValueError,'reviewed source'):
            reviewed_gate(changed,manifest['nativeQualificationHarnessCommit'],solver,build)
        row=json.loads(files['unit/pinning/result.json']);row['gateSha256']='0'*64
        files['unit/pinning/result.json']=json.dumps(row)
        self.reject_rehashed(files,solver,build,gate,'gate checksum')

    def reject_rehashed(self,files,solver,build,gate,message):
        # Rehash all outer claims too: the expected rejection must come from the
        # independently reviewed case/gate, not just a stale archive/member hash.
        for stage in ('pinning','round0','round1'):
            prefix='unit/'+stage+'/'
            row=json.loads(files[prefix+'result.json'])
            row['files']={name[len(prefix):]:sha(value.encode()) for name,value in files.items()
                          if name.startswith(prefix) and Path(name).name!='result.json'}
            files[prefix+'result.json']=json.dumps(row)
        top=json.loads(files['unit/result.json'])
        for row in top['stages']:row['resultSha256']=sha(files['unit/'+row['resultPath']].encode())
        files['unit/result.json']=json.dumps(top)
        raw=gzip.compress(json.dumps(files).encode())
        with self.assertRaisesRegex(ValueError,message):native_rows(raw,sha(raw),solver,build,gate)

    def test_placeholders_duplicates_missing_invocations_and_changed_hits_are_rejected(self):
        solver,build,gate,original,*_=self.inputs()
        for kind in ('placeholders','duplicate-label','missing-call','different-hit'):
            files=copy.deepcopy(original);prefix='unit/pinning/'
            if kind in ('placeholders','duplicate-label'):
                row=json.loads(files[prefix+'result.json'])
                row['correctness']=([{'pass':True}]*13 if kind=='placeholders' else [row['correctness'][0]]*13)
                files[prefix+'result.json']=json.dumps(row)
            elif kind=='missing-call':del files[prefix+'small-cases/00/invocation.json']
            else:files[prefix+'small-cases/00/hits.txt']='forged candidate\n'
            with self.subTest(kind=kind):self.reject_rehashed(files,solver,build,gate,'Native (correctness row|small-case)')

    def test_historical_a10g_cases_cannot_be_relabelled_as_l4(self):
        solver,build,gate,files,*_=self.inputs()
        gate=copy.deepcopy(gate);gate['nativeDeviceName']='L4'
        self.reject_rehashed(files,solver,build,gate,'completion/device differs')

    def test_full_unit_device_cannot_override_its_retained_native_log(self):
        solver,build,gate,files,*_=self.inputs()
        path='unit/pinning/result.json';row=json.loads(files[path])
        row['unit']['device'][0]['device']='NVIDIA L4';files[path]=json.dumps(row)
        self.reject_rehashed(files,solver,build,gate,'full-unit device differs')


class ArchiveDurabilityTests(unittest.TestCase):
    def script(self):
        raw=(ROOT/'ops/aws-gpu-execution/host-pqb-final-image.sh').read_text()
        return compile(raw.split('python3 - "$results" <<\'PY\'\n',1)[1].split('\nPY',1)[0],'native-collector','exec')

    def test_metadata_is_only_emitted_after_durable_atomic_publication(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'result.txt').write_text('public receipt')
            events=[];real_sync,real_replace=os.fsync,Path.replace
            def sync(fd):
                events.append('directory-sync' if stat.S_ISDIR(os.fstat(fd).st_mode) else 'file-sync');real_sync(fd)
            def replace(src,dst):events.append('rename');return real_replace(src,dst)
            class Output(io.StringIO):
                def write(self,value):
                    if value.startswith('QSB_PUBLIC_RESULT_META='):events.append('metadata')
                    return super().write(value)
            output=Output()
            with mock.patch.object(sys,'argv',['collector',str(root)]),mock.patch('os.fsync',sync), \
                 mock.patch.object(Path,'replace',replace),contextlib.redirect_stdout(output):
                exec(self.script(),{})
            self.assertEqual(events,['file-sync','rename','directory-sync','metadata'])
            archive=(root/'public-result.json.gz').read_bytes()
            self.assertEqual(json.loads(gzip.decompress(archive)),{'result.txt':'public receipt'})
            meta=json.loads(output.getvalue().split('=',1)[1]);self.assertEqual(meta,{'bytes':len(archive),'sha256':sha(archive)})

    def test_sync_failure_never_prints_completion_metadata(self):
        for fail_at in (1,2):
            with self.subTest(fail_at=fail_at),tempfile.TemporaryDirectory() as temp:
                root=Path(temp);(root/'result.txt').write_text('public receipt');output=io.StringIO();count=0;real_sync=os.fsync
                def sync(fd):
                    nonlocal count
                    count+=1
                    if count==fail_at:raise OSError('simulated storage failure')
                    real_sync(fd)
                with mock.patch.object(sys,'argv',['collector',str(root)]),mock.patch('os.fsync',sync), \
                     contextlib.redirect_stdout(output),self.assertRaises(OSError):exec(self.script(),{})
                self.assertNotIn('QSB_PUBLIC_RESULT_META',output.getvalue())
