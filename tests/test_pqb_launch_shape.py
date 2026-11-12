import importlib.util
from pathlib import Path
import unittest
from unittest.mock import Mock

ROOT=Path(__file__).resolve().parents[1]
spec=importlib.util.spec_from_file_location('pqb_shape_control',ROOT/'ops/aws-gpu-execution/control.py')
control=importlib.util.module_from_spec(spec);spec.loader.exec_module(control)


class LaunchShapeTests(unittest.TestCase):
    def test_auto_placement_requires_default_vpc_and_safe_default_subnets(self):
        config=dict(vpc='vpc-test',subnet='subnet-test')
        call=Mock(side_effect=[dict(Vpcs=[dict(VpcId='vpc-test',IsDefault=True)]),
                              dict(Subnets=[dict(VpcId='vpc-test',DefaultForAz=True,MapPublicIpOnLaunch=True)])])
        self.assertEqual(control.placement_options(call,config,True),{})
        self.assertEqual(control.placement_options(Mock(),config,False),dict(SubnetId='subnet-test'))
        for defaults in [[],[dict(VpcId='wrong',DefaultForAz=True,MapPublicIpOnLaunch=True)],
                         [dict(VpcId='vpc-test',DefaultForAz=True,MapPublicIpOnLaunch=False)]]:
            call=Mock(side_effect=[dict(Vpcs=[dict(VpcId='vpc-test',IsDefault=True)]),dict(Subnets=defaults)])
            with self.assertRaises(ValueError):control.placement_options(call,config,True)

    def shape(self,**changes):
        return dict(InstanceType='g5.4xlarge',GpuInfo=dict(Gpus=[dict(Name='A10G',Count=1)]),
                    ProcessorInfo=dict(SupportedArchitectures=['x86_64']),VCpuInfo=dict(DefaultVCpus=16),**changes)

    def test_one_a10g_and_actual_cpu_quota(self):
        shape=self.shape();call=Mock(return_value=dict(InstanceTypes=[shape]))
        self.assertEqual(control.qualified_shape(call,'g5.4xlarge',16),shape)
        call.assert_called_with('ec2','describe-instance-types',InstanceTypes=['g5.4xlarge'])
        with self.assertRaisesRegex(ValueError,'Quota'):control.qualified_shape(call,'g5.4xlarge',15)

    def test_wrong_device_multiple_gpus_or_architecture_is_refused(self):
        for field,value in [('GpuInfo',dict(Gpus=[dict(Name='A100',Count=1)])),
                            ('GpuInfo',dict(Gpus=[dict(Name='A10G',Count=4)])),
                            ('ProcessorInfo',dict(SupportedArchitectures=['arm64']))]:
            shape=self.shape();shape[field]=value
            with self.subTest(field=field),self.assertRaises(ValueError):
                control.qualified_shape(Mock(return_value=dict(InstanceTypes=[shape])),'g5.4xlarge',64)
        call=Mock()
        with self.assertRaises(ValueError):control.qualified_shape(call,'g5.12xlarge',64)
        call.assert_not_called()
