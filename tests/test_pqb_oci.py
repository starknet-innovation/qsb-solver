import hashlib
import importlib.util
import io
import json
from pathlib import Path
import sys
import subprocess
import tarfile
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from pqb_oci import inspect


class OciIdentityTests(unittest.TestCase):
    def archive(self, change=None, corrupt=False):
        blobs = {}
        def blob(data, media):
            raw = data if isinstance(data,bytes) else json.dumps(data).encode()
            digest = hashlib.sha256(raw).hexdigest()
            blobs['blobs/sha256/'+digest] = raw
            return dict(digest='sha256:'+digest,size=len(raw),mediaType=media)
        config = blob(dict(architecture='amd64',os='linux',config=dict(WorkingDir='/opt/qsb-pqb',
                           Cmd=['python3','aws_entrypoint.py'])), 'application/vnd.oci.image.config.v1+json')
        layer = blob(b'layer bytes', 'application/vnd.oci.image.layer.v1.tar+gzip')
        manifest = blob(dict(schemaVersion=2,config=config,layers=[layer]),'application/vnd.oci.image.manifest.v1+json')
        manifest['platform'] = dict(architecture='amd64',os='linux')
        index = dict(schemaVersion=2,manifests=[manifest])
        if change:
            change(index)
        root = blob(index,'application/vnd.oci.image.index.v1+json')
        blobs['index.json'] = json.dumps(dict(schemaVersion=2,manifests=[root])).encode()
        blobs['oci-layout'] = b'{"imageLayoutVersion":"1.0.0"}'
        if corrupt:
            blobs['blobs/sha256/'+config['digest'][7:]] += b'changed'
        temp = tempfile.NamedTemporaryFile(suffix='.tar',delete=False)
        self.addCleanup(lambda:Path(temp.name).unlink(missing_ok=True))
        temp.close()
        with tarfile.open(temp.name,'w') as tar:
            for name, raw in blobs.items():
                member=tarfile.TarInfo(name);member.size=len(raw)
                tar.addfile(member,io.BytesIO(raw))
        return Path(temp.name),root,config

    def test_registry_subject_is_exact_manifest_digest_not_config(self):
        path,root,config = self.archive()
        identity,raw,cfg = inspect(path)
        self.assertEqual(identity['imageDigest'],root['digest'])
        self.assertEqual(identity['configDigest'],config['digest'])
        self.assertEqual('sha256:'+hashlib.sha256(raw).hexdigest(),root['digest'])
        self.assertNotEqual(identity['imageDigest'],identity['configDigest'])
        self.assertEqual(json.loads(cfg)['config']['WorkingDir'],'/opt/qsb-pqb')

    def test_corrupt_blob_is_rejected(self):
        path,_,_ = self.archive(corrupt=True)
        with self.assertRaisesRegex(ValueError,'blob hash mismatch'):
            inspect(path)

    def test_wrong_or_duplicate_platform_is_rejected(self):
        for change in [lambda d:d['manifests'][0]['platform'].update(architecture='arm64'),
                       lambda d:d['manifests'].append(d['manifests'][0])]:
            path,_,_=self.archive(change)
            with self.assertRaisesRegex(ValueError,'exactly one linux/amd64'):
                inspect(path)

    def test_link_or_traversal_archive_member_is_rejected(self):
        for name,kind in [('../escape',tarfile.REGTYPE),('link',tarfile.SYMTYPE)]:
            path,_,_=self.archive()
            with tarfile.open(path,'a') as tar:
                member=tarfile.TarInfo(name);member.type=kind;tar.addfile(member)
            with self.assertRaises(ValueError):inspect(path)


class FinalImageGateTests(unittest.TestCase):
    def test_imported_runtime_uses_rootfs_and_config_not_docker_store_id(self):
        script=(ROOT/'ops/aws-gpu-execution/host-pqb-final-image.sh').read_text()
        block=script.split('python3 - "$bundle" "$results" <<\'PY\'\n',1)[1].split('\nPY',1)[0]
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'gate').mkdir();results=root/'results';results.mkdir()
            identity=dict(imageDigest='sha256:'+'a'*64,configDigest='sha256:'+'b'*64)
            config=dict(architecture='amd64',os='linux',rootfs=dict(diff_ids=['sha256:'+'c'*64]),
                        config=dict(WorkingDir='/opt/qsb-pqb',Cmd=['python3','aws_entrypoint.py'],Env=['PATH=/usr/bin']))
            image=dict(Id=identity['imageDigest'],Architecture='amd64',Os='linux',
                       RootFS=dict(Layers=config['rootfs']['diff_ids']),Config=config['config'])
            (root/'gate/oci-identity.json').write_text(json.dumps(identity))
            (root/'image-config.json').write_text(json.dumps(config))
            def run():
                (results/'image.json').write_text(json.dumps([image]))
                return subprocess.run([sys.executable,'-',str(root),str(results)],input=block,text=True,capture_output=True)
            self.assertEqual(run().returncode,0)
            self.assertTrue(json.loads((results/'runtime-identity-check.json').read_text())['rootfsDiffIdsMatched'])
            image['RootFS']['Layers']=['sha256:'+'d'*64]
            self.assertNotEqual(run().returncode,0)
            image['RootFS']['Layers']=config['rootfs']['diff_ids']
            image['Config']={**config['config'],'Env':['PATH=/unexpected']}
            self.assertNotEqual(run().returncode,0)

    def test_corrupt_or_linked_public_gate_is_refused_before_worker_import(self):
        spec=importlib.util.spec_from_file_location('qualify',ROOT/'research/pqb-ranked/measure/qualify_image.py')
        mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
        with tempfile.TemporaryDirectory() as tmp:
            gate=Path(tmp)
            p=gate/'qualify_image.py';p.write_text('changed')
            (gate/'SHA256SUMS').write_text('0'*64+'  qualify_image.py\n')
            with self.assertRaisesRegex(ValueError,'Invalid public gate input'):mod.verify_gate(gate)
            p.unlink();p.symlink_to(ROOT/'research/pqb-ranked/measure/qualify_image.py')
            (gate/'SHA256SUMS').write_text(mod.sha(p)+'  qualify_image.py\n')
            with self.assertRaisesRegex(ValueError,'Invalid public gate input'):mod.verify_gate(gate)
