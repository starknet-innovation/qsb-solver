import hashlib,importlib.util,io,json,pathlib,unittest
spec=importlib.util.spec_from_file_location('aws_entrypoint',pathlib.Path(__file__).resolve().parents[1]/'worker/aws/entrypoint.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
class AwsTransportTest(unittest.TestCase):
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
