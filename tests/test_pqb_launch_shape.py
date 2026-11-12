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
        with self.assertRaises(ValueError):control.qualified_shape(call,'g5.48xlarge',192)
        call.assert_not_called()

    def test_explicit_four_a10g_host_requires_its_full_quota_and_isolates_one_gpu(self):
        shape=self.shape();shape.update(InstanceType='g5.12xlarge',
            GpuInfo=dict(Gpus=[dict(Name='A10G',Count=4)]),VCpuInfo=dict(DefaultVCpus=48))
        call=Mock(return_value=dict(InstanceTypes=[shape]))
        self.assertEqual(control.qualified_shape(call,'g5.12xlarge',48),shape)
        with self.assertRaisesRegex(ValueError,'Quota'):control.qualified_shape(call,'g5.12xlarge',47)
        for count in (1,8):
            wrong={**shape,'GpuInfo':dict(Gpus=[dict(Name='A10G',Count=count)])}
            with self.subTest(count=count),self.assertRaises(ValueError):
                control.qualified_shape(Mock(return_value=dict(InstanceTypes=[wrong])),'g5.12xlarge',64)
        host=(ROOT/'ops/aws-gpu-execution/host-pqb-final-image.sh').read_text()
        self.assertIn('--gpus device=0',host)
        self.assertNotIn('--gpus all',host)
        self.assertIn('gpu-inventory.txt',host)
        self.assertIn('nvidia-smi --id=0',host)

    def test_l4_scope_requires_one_full_device_and_its_quota(self):
        shape=self.shape();shape.update(InstanceType='g6.2xlarge',
            GpuInfo=dict(Gpus=[dict(Name='L4',Count=1,GpuPartitionSize=1)]),VCpuInfo=dict(DefaultVCpus=8))
        self.assertEqual(control.qualified_shape(Mock(return_value=dict(InstanceTypes=[shape])),'g6.2xlarge',8),shape)
        with self.assertRaisesRegex(ValueError,'Quota'):
            control.qualified_shape(Mock(return_value=dict(InstanceTypes=[shape])),'g6.2xlarge',7)
        for gpu in (dict(Name='A10G',Count=1),dict(Name='L4',Count=0,GpuPartitionSize=.25),
                    dict(Name='L4',Count=1,GpuPartitionSize=.5)):
            wrong={**shape,'GpuInfo':dict(Gpus=[gpu])}
            with self.subTest(gpu=gpu),self.assertRaises(ValueError):
                control.qualified_shape(Mock(return_value=dict(InstanceTypes=[wrong])),'g6.2xlarge',8)
