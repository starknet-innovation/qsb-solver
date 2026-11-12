import hashlib,importlib.util,io,json,pathlib,unittest
import sys,types
from unittest import mock
spec=importlib.util.spec_from_file_location('aws_entrypoint',pathlib.Path(__file__).resolve().parents[1]/'worker/aws/entrypoint.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
class AwsTransportTest(unittest.TestCase):
 def test_client_uses_updated_system_roots_and_preserves_single_attempt(self):
  created={};client=object();handler=object()
  def config(**kwargs):created['config']=kwargs;return kwargs
  def factory(service,**kwargs):created.update(service=service,options=kwargs);return client
  modules={'boto3':types.SimpleNamespace(client=factory),
           'botocore':types.ModuleType('botocore'),
           'botocore.config':types.SimpleNamespace(Config=config),
           'handler':types.SimpleNamespace(handler=handler)}
  with mock.patch.dict(sys.modules,modules),mock.patch.dict(module.os.environ,{'AWS_CA_BUNDLE':'/untrusted/override.pem'}),mock.patch.object(module,'run') as run:
   module.main()
   run.assert_called_once_with(client,handler,module.os.environ)
  self.assertEqual(created['service'],'s3')
  self.assertEqual(created['options']['verify'],'/etc/ssl/certs/ca-certificates.crt')
  self.assertEqual(created['config'],dict(connect_timeout=5,read_timeout=15,retries={'mode':'standard','total_max_attempts':1}))
 def setUp(self):
  self.raw=json.dumps({'input':{'public':'synthetic'}}).encode();self.calls=[]
  self.env={'AWS_BATCH_JOB_ID':'12345678-1234-1234-1234-123456789abc','QSB_JOB_BUCKET':'isolated','QSB_INPUT_KEY':'inputs/12345678-1234-1234-1234-123456789abc.json','QSB_INPUT_SHA256':hashlib.sha256(self.raw).hexdigest()}
 def get_object(self,**kwargs):return {'ContentLength':len(self.raw),'Body':io.BytesIO(self.raw)}
 def put_object(self,**kwargs):self.calls.append(kwargs)
 def test_bound_input_and_immutable_output(self):
  module.run(self,lambda event:{'status':'completed'},self.env)
  self.assertEqual(self.calls[0]['IfNoneMatch'],'*');result=json.loads(self.calls[0]['Body']);self.assertEqual(result['jobId'],self.env['AWS_BATCH_JOB_ID']);self.assertEqual(result['inputSha256'],self.env['QSB_INPUT_SHA256'])
 def test_tampered_input_never_computes(self):
  self.raw+=b' '
  with self.assertRaisesRegex(ValueError,'identity'):module.run(self,lambda _:self.fail('GPU invoked'),self.env)
  self.assertEqual(self.calls,[])
 def test_unknown_fields_never_compute(self):
  self.raw=json.dumps({'input':{},'private':'forbidden'}).encode();self.env['QSB_INPUT_SHA256']=hashlib.sha256(self.raw).hexdigest()
  with self.assertRaisesRegex(ValueError,'envelope'):module.run(self,lambda _:self.fail('GPU invoked'),self.env)
