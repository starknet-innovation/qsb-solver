"""Review fixes in the PQB operations code: no AWS call, credentials or Docker."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import sys
import tempfile
import types
import subprocess
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, ROOT / path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class LambdaListingTest(unittest.TestCase):
    def setUp(self):
        sys.path.insert(0, str(ROOT / 'ops/pqb-public-solve'))
        self.addCleanup(sys.path.remove, str(ROOT / 'ops/pqb-public-solve'))
        self.control = load('pqb_public_solve_control', 'ops/pqb-public-solve/control.py')

    def pages(self, target_page):
        calls = []

        def call(service, operation, **params):
            calls.append(params)
            page = int(params.get('Marker', '0'))
            names = ['other-%d-%d' % (page, i) for i in range(50)]
            if page == target_page:
                names[7] = 'qsb-pqb-solve-0123abcd'
            return {'Functions': [{'FunctionName': n} for n in names], **({'NextMarker': str(page + 1)} if page < 2 else {})}
        return call, calls

    def test_a_function_beyond_the_first_page_is_found(self):
        call, calls = self.pages(2)
        self.assertTrue(self.control.function_exists(call, 'qsb-pqb-solve-0123abcd'))
        self.assertEqual(calls, [{}, {'Marker': '1'}, {'Marker': '2'}])

    def test_absent_only_after_every_page(self):
        call, calls = self.pages(99)
        self.assertFalse(self.control.function_exists(call, 'qsb-pqb-solve-0123abcd'))
        self.assertEqual(len(calls), 3)


class LaunchTemplateLookupTest(unittest.TestCase):
    """Removal after an arm that failed before recording the launch template id."""

    def setUp(self):
        sys.path.insert(0, str(ROOT / 'ops/pqb-public-solve'))
        self.addCleanup(sys.path.remove, str(ROOT / 'ops/pqb-public-solve'))
        self.control = load('pqb_public_solve_control_lt', 'ops/pqb-public-solve/control.py')

    def call(self, by_name, by_id=()):
        def call(service, operation, **params):
            self.assertEqual((service, operation), ('ec2', 'describe-launch-templates'))
            f = params['Filters'][0]
            ids = by_name if f['Name'] == 'launch-template-name' else [i for i in by_id if i in f['Values']]
            return {'LaunchTemplates': [{'LaunchTemplateId': i} for i in ids]}
        return call

    def test_created_but_never_recorded(self):
        self.assertEqual(self.control.launch_template_ids(self.call(['lt-1']), 'qsb-pqb-solve-0123abcd'), ['lt-1'])

    def test_never_created(self):
        self.assertEqual(self.control.launch_template_ids(self.call([]), 'qsb-pqb-solve-0123abcd'), [])

    def test_recorded_and_present_once(self):
        self.assertEqual(self.control.launch_template_ids(self.call(['lt-1'], ['lt-1']), 'n', 'lt-1'), ['lt-1'])

    def test_recorded_but_already_deleted(self):
        self.assertEqual(self.control.launch_template_ids(self.call([], []), 'n', 'lt-1'), [])

    def test_remove_no_longer_reads_the_id_from_state_unconditionally(self):
        text = (ROOT / 'ops/pqb-public-solve/control.py').read_text()
        self.assertNotIn("LaunchTemplateId=s['launchTemplateId'])", text)


class CleanupFunctionCodeTest(unittest.TestCase):
    """The GPU controller's CreateFunction request is the request that is made, in either transport."""

    def setUp(self):
        sys.path.insert(0, str(ROOT / 'ops/aws-gpu-execution'))
        sys.path.insert(0, str(ROOT / 'ops/aws-gpu-benchmark'))
        self.addCleanup(sys.path.remove, str(ROOT / 'ops/aws-gpu-execution'))
        self.addCleanup(sys.path.remove, str(ROOT / 'ops/aws-gpu-benchmark'))
        self.control = load('qsb_gpu_control_code', 'ops/aws-gpu-execution/control.py')
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def test_archive_is_the_same_bytes_every_time_and_holds_the_cleanup_source(self):
        import zipfile
        first = self.control.cleanup_archive(self.tmp.name).read_bytes()
        os.utime(ROOT / 'ops/aws-gpu-execution/cleanup.py')                # a changed timestamp must not matter
        second = self.control.cleanup_archive(self.tmp.name).read_bytes()
        self.assertEqual(first, second)
        with zipfile.ZipFile(Path(self.tmp.name) / 'cleanup.zip') as z:
            self.assertEqual(z.namelist(), ['cleanup.py'])
            self.assertEqual(z.read('cleanup.py'), (ROOT / 'ops/aws-gpu-execution/cleanup.py').read_bytes())

    def test_cli_sends_the_zip_inline_and_mcp_names_the_staged_object(self):
        import base64
        archive = self.control.cleanup_archive(self.tmp.name)
        self.assertEqual(self.control.function_code(archive, {}),
                         {'ZipFile': base64.b64encode(archive.read_bytes()).decode()})
        mcp = {'QSB_AWS_MCP_RPC_DIR': '/receipts', 'QSB_CLEANUP_CODE_S3_BUCKET': 'b', 'QSB_CLEANUP_CODE_S3_KEY': 'k/cleanup.zip'}
        self.assertEqual(self.control.function_code(archive, mcp), {'S3Bucket': 'b', 'S3Key': 'k/cleanup.zip'})
        for missing in ('QSB_CLEANUP_CODE_S3_BUCKET', 'QSB_CLEANUP_CODE_S3_KEY'):
            with self.assertRaisesRegex(ValueError, 'staged cleanup archive'):
                self.control.function_code(archive, {k: v for k, v in mcp.items() if k != missing})

    def test_the_code_is_settled_before_the_deadline_starts(self):
        text = (ROOT / 'ops/aws-gpu-execution/control.py').read_text()
        arm = text.index("if args.mode=='arm':")
        self.assertLess(text.index('code=function_code(archive,os.environ)', arm), text.index("phase='arming'", arm))
        self.assertNotIn("Code={'ZipFile'", text[arm:])


class ResumableRemovalTest(unittest.TestCase):
    def setUp(self):
        sys.path.insert(0, str(ROOT / 'ops/pqb-public-solve'))
        self.addCleanup(sys.path.remove, str(ROOT / 'ops/pqb-public-solve'))
        self.control = load('pqb_public_solve_control_rm', 'ops/pqb-public-solve/control.py')

    def test_an_already_deleted_resource_does_not_stop_removal(self):
        for message in ('An error occurred (NoSuchEntity) when calling the DeleteRole operation: The role cannot be found.',
                        'RepositoryNotFoundException: The repository does not exist', 'NoSuchBucket',
                        'InvalidGroup.NotFound: The security group does not exist',
                        'ResourceNotFoundException: The specified log group does not exist.'):
            def call(service, operation, **params):
                raise RuntimeError(message)
            self.control.delete(call, 'iam', 'delete-role', RoleName='x')      # tolerated

    def test_any_other_failure_still_stops_it(self):
        for message in ('DependencyViolation: resource has a dependent object', 'AccessDenied', 'Throttling: Rate exceeded'):
            def call(service, operation, **params):
                raise RuntimeError(message)
            with self.assertRaises(RuntimeError):
                self.control.delete(call, 'ec2', 'delete-security-group', GroupId='sg-1')

    def test_unrecorded_job_definitions_are_found_by_name_across_pages(self):
        seen = []

        def call(service, operation, **params):
            seen.append(params)
            self.assertEqual((service, operation, params['jobDefinitionName'], params['status']),
                             ('batch', 'describe-job-definitions', 'qsb-pqb-solve-0123abcd', 'ACTIVE'))
            if 'nextToken' not in params:
                return {'jobDefinitions': [{'jobDefinitionArn': 'arn:1'}], 'nextToken': 't'}
            return {'jobDefinitions': [{'jobDefinitionArn': 'arn:2'}]}
        self.assertEqual(self.control.job_definitions(call, 'qsb-pqb-solve-0123abcd'), ['arn:1', 'arn:2'])
        self.assertEqual(len(seen), 2)

    def test_remove_guards_every_deletion(self):
        text = (ROOT / 'ops/pqb-public-solve/control.py').read_text()
        remove = text[text.index("elif a.mode=='remove':"):text.index("phase='removed'")]
        import re
        unguarded = [m for m in re.findall(r"(?<!delete\()call\('[a-z0-9]+','(?:delete|deregister|remove|detach)[a-z-]+'", remove)]
        self.assertEqual(unguarded, [])


class LaterReviewFixesTest(unittest.TestCase):
    def setUp(self):
        sys.path.insert(0, str(ROOT / 'ops/pqb-public-solve'))
        self.addCleanup(sys.path.remove, str(ROOT / 'ops/pqb-public-solve'))
        self.control = load('pqb_public_solve_control_later', 'ops/pqb-public-solve/control.py')

    def test_an_unrecorded_security_group_is_found_by_name_and_vpc(self):
        def call(service, operation, **params):
            self.assertEqual((service, operation), ('ec2', 'describe-security-groups'))
            self.assertEqual(params['Filters'], [{'Name': 'group-name', 'Values': ['qsb-pqb-solve-0123abcd']},
                                                 {'Name': 'vpc-id', 'Values': ['vpc-1']}])
            return {'SecurityGroups': [{'GroupId': 'sg-9'}]}
        self.assertEqual(self.control.security_group_ids(call, 'qsb-pqb-solve-0123abcd', 'vpc-1'), ['sg-9'])
        self.assertEqual(self.control.security_group_ids(call, 'qsb-pqb-solve-0123abcd', 'vpc-1', 'sg-9'), ['sg-9'])
        self.assertEqual(self.control.security_group_ids(lambda *a, **k: {'SecurityGroups': []}, 'n', 'vpc-1', 'sg-2'), ['sg-2'])

    def test_public_solve_archive_is_stable_and_built_before_the_arm_is_consumed(self):
        with tempfile.TemporaryDirectory() as tmp:
            first = self.control.cleanup_archive(tmp).read_bytes()
            os.utime(ROOT / 'ops/pqb-public-solve/cleanup.py')
            self.assertEqual(self.control.cleanup_archive(tmp).read_bytes(), first)
        text = (ROOT / 'ops/pqb-public-solve/control.py').read_text()
        arm = text.index("elif a.mode=='arm':")
        self.assertLess(text.index('archive=cleanup_archive(path.parent)', arm), text.index("phase='arming'", arm))
        prepare = text[:arm]
        self.assertIn('cleanupCodeSha256=', prepare)

    def test_full_unit_receipts_are_flushed(self):
        runner = load('pqb_run_full_unit_flush', 'research/pqb-ranked/measure/run_full_unit.py')
        events = []
        real = os.fsync

        def fsync(fd):
            import stat
            events.append('dir' if stat.S_ISDIR(os.fstat(fd).st_mode) else 'file')
            return real(fd)
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(runner.os, 'fsync', fsync):
            path = Path(tmp) / 'result.json'
            runner.write_json(path, {'status': 'passed'})
            self.assertEqual(json.loads(path.read_text()), {'status': 'passed'})
            self.assertEqual(events, ['file', 'dir'])
            self.assertEqual([p.name for p in Path(tmp).iterdir()], ['result.json'])

    def test_the_upstream_baseline_is_bound_before_it_is_compiled(self):
        text = (ROOT / 'worker/pqb/build.py').read_text()
        check = text.index("lock['upstream']['adaptedFromSha256']")
        self.assertLess(check, text.index("subprocess.run(['nvcc']"))
        lock = json.loads((ROOT / 'research/pqb-ranked/source-lock.json').read_text())
        self.assertEqual(hashlib.sha256((ROOT / 'vendor/pqb/grinder/grind.cu').read_bytes()).hexdigest(),
                         lock['upstream']['adaptedFromSha256'])
        # the measure stage compiles that file from the build stage, after build.py has run
        docker = (ROOT / 'worker/pqb/Dockerfile').read_text()
        self.assertLess(docker.index('python3 /src/worker/pqb/build.py'), docker.index('grind-upstream'))

    def test_the_controller_checks_gate_hits_against_the_unit_size(self):
        text = (ROOT / 'ops/pqb-public-solve/controller.ts').read_text()
        self.assertIn('(result.output as any)?.gateHits', text)
        self.assertIn('6*Math.sqrt(gateMean)+6', text)
        self.assertIn('{pinning:72,round1:192,round2:64}', text)
        self.assertNotIn('gateHits:0', (ROOT / 'ops/pqb-public-solve/self_test.ts').read_text())


class DurableRequestTest(unittest.TestCase):
    def test_request_is_flushed_before_it_is_published(self):
        rpc = load('qsb_mcp_rpc_durable', 'ops/aws-gpu-execution/mcp_rpc.py')
        events = []
        real_fsync, real_rename = os.fsync, Path.rename

        def fsync(fd):
            events.append('fsync-dir' if os.path.isdir('/dev/fd/%d' % fd) or _is_dir(fd) else 'fsync-file')
            return real_fsync(fd)

        def rename(self, target):
            events.append('rename')
            return real_rename(self, target)

        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(rpc.os, 'fsync', fsync), \
                mock.patch.object(Path, 'rename', rename):
            with self.assertRaises(TimeoutError):
                rpc.exchange(tmp, 'eu-west-1', 'ec2', 'run-instances', {'ClientToken': 'x'}, timeout=0)
            self.assertEqual(events, ['fsync-file', 'rename', 'fsync-dir'])
            self.assertEqual(len(list(Path(tmp).glob('*.request.json'))), 1)
            self.assertEqual(list(Path(tmp).glob('*.partial')), [])


def _is_dir(fd):
    import stat
    return stat.S_ISDIR(os.fstat(fd).st_mode)


class PublisherFailureTest(unittest.TestCase):
    def setUp(self):
        # the publisher imports boto3 lazily; these stand-ins are never called before the failure
        for name in ('boto3', 'botocore', 'botocore.config'):
            if name not in sys.modules:
                sys.modules[name] = types.ModuleType(name)
                self.addCleanup(sys.modules.pop, name)
        if not hasattr(sys.modules['botocore.config'], 'Config'):
            sys.modules['botocore.config'].Config = lambda **options: options
        self.publisher = load('pqb_publish_private', 'ops/pqb-public-solve/publish_private.py')
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.artifact = Path(self.tmp.name) / 'artifact'
        self.artifact.mkdir()
        for name in ('image.tar.gz', 'image.json', 'binding.json', 'source-commit'):
            (self.artifact / name).write_text(name)
        self.repository = '123456789012.dkr.ecr.eu-west-1.amazonaws.com/qsb-pqb-solve-0123abcd'

    def sums(self, **wrong):
        (self.artifact / 'SHA256SUMS').write_text(''.join(
            '%s  %s\n' % (wrong.get(n, hashlib.sha256((self.artifact / n).read_bytes()).hexdigest()), n)
            for n in ('image.tar.gz', 'image.json', 'binding.json', 'source-commit')))

    def test_the_marker_is_exclusive_and_flushed_before_anything_else(self):
        text = (ROOT / 'ops/pqb-public-solve/publish_private.py').read_text()
        body = text[text.index('def publish'):]
        marker = body.index("with open(output, 'x') as marker:")
        self.assertLess(marker, body.index('os.fsync(marker.fileno())'))
        self.assertLess(body.index('os.fsync(marker.fileno())'), body.index('os.fsync(marker_directory)'))
        for later in ("(artifact/'SHA256SUMS')", "'docker','load'", "'docker','push'"):
            self.assertLess(body.index('os.fsync(marker_directory)'), body.index(later), later)
        self.assertNotIn('output.write_text(', text)

    def test_a_failure_after_the_marker_leaves_a_terminal_receipt(self):
        self.sums(**{'image.json': '0' * 64})
        output = Path(self.tmp.name) / 'receipt.json'
        with self.assertRaisesRegex(ValueError, 'Artifact hash mismatch'):
            self.publisher.publish(self.artifact, self.repository, 'eu-west-1', output)
        receipt = json.loads(output.read_text())
        self.assertEqual((receipt['status'], receipt['stage'], receipt['registryStateUncertain']),
                         ('failed', 'verifying the artifact', False))
        self.assertIn('Artifact hash mismatch: image.json', receipt['error'])
        with self.assertRaisesRegex(ValueError, 'already exists'):          # still one-shot
            self.publisher.publish(self.artifact, self.repository, 'eu-west-1', output)

    def test_the_success_receipt_replaces_the_marker_atomically(self):
        text = (ROOT / 'ops/pqb-public-solve/publish_private.py').read_text()
        self.assertIn("replace_durably(output, receipt, '.published.tmp')", text)
        # nothing writes the success receipt over the marker in place
        self.assertNotIn('output.write_text(', text)                           # nothing is written in place

    def test_full_unit_host_script_arms_its_trap_with_the_marker(self):
        text = (ROOT / 'ops/aws-gpu-execution/host-pqb-full-unit.sh').read_text()
        lines = text.splitlines()
        marker = next(i for i, ln in enumerate(lines) if ln.startswith('mkdir "$results"'))
        self.assertTrue(lines[marker + 1].startswith('trap collect EXIT'))
        self.assertLess(text.index('collect() {'), text.index('mkdir "$results"'))
        # the receipt records the failing command's own status (e.g. 124 for a pull timeout), read on
        # entry to the handler before Docker cleanup can replace it
        body = lines[lines.index('collect() {') + 1]
        self.assertTrue(body.strip().startswith('status=$?'))
        self.assertNotIn('status=1', text)

    def test_exit_trap_idiom_keeps_the_failing_status(self):
        script = 'set -euo pipefail\ncollect() {\n  status=$?\n  true || true\n  echo "$status"\n}\n' \
                 'trap collect EXIT\n(exit 124)\n'
        done = subprocess.run(['bash', '-c', script], capture_output=True, text=True)
        self.assertEqual((done.returncode, done.stdout), (124, '124\n'))

    def test_export_keeps_only_the_selected_chain(self):
        text = (ROOT / 'ops/pqb-public-solve/export-reference.ts').read_text()
        self.assertNotIn('state.solutions.map(', text)
        self.assertIn('selectedRecords(state, input)', text)
        self.assertTrue((ROOT / 'ops/pqb-public-solve/self_test_export.ts').is_file())

    def test_the_failure_receipt_is_flushed_like_the_success_receipt(self):
        text = (ROOT / 'ops/pqb-public-solve/publish_private.py').read_text()
        body = text[text.index('def publish'):]
        self.assertEqual(body.count('replace_durably(output, '), 2)            # success and failure
        helper = text[text.index('def replace_durably'):text.index('def publish')]
        self.assertLess(helper.index('os.fsync(stream.fileno())'), helper.index('temporary.replace(output)'))
        self.assertLess(helper.index('temporary.replace(output)'), helper.index('os.fsync(directory_fd)'))

    def test_a_failure_after_the_push_started_is_marked_uncertain(self):
        self.sums()
        (self.artifact / 'image.json').write_text(json.dumps([{'Id': 'sha256:abc'}]))
        binding = {'solverCommit': 'source-commit', 'status': 'HOLD', 'cudaArchitecture': '86'}
        (self.artifact / 'binding.json').write_text(json.dumps(binding))
        self.sums()
        output = Path(self.tmp.name) / 'receipt.json'

        def run(command, **kwargs):
            if command[:2] == ['docker', 'push']:
                raise RuntimeError('connection reset during push')
            return mock.Mock(returncode=0)

        def check_output(command, **kwargs):
            return 'sha256:abc\n' if 'inspect' in command else json.dumps(binding)

        client = mock.Mock()
        client.get_authorization_token.return_value = {'authorizationData': [{'authorizationToken': 'dTpw'}]}
        # patched, not assigned: a real installed boto3 keeps its own client afterwards
        with mock.patch.object(sys.modules['boto3'], 'client', lambda *a, **k: client, create=True), \
                mock.patch.object(self.publisher.subprocess, 'run', run), \
                mock.patch.object(self.publisher.subprocess, 'check_output', check_output):
            with self.assertRaisesRegex(RuntimeError, 'connection reset'):
                self.publisher.publish(self.artifact, self.repository, 'eu-west-1', output)
        receipt = json.loads(output.read_text())
        self.assertEqual((receipt['status'], receipt['stage'], receipt['registryStateUncertain']),
                         ('failed', 'pushing', True))


if __name__ == '__main__':
    unittest.main()
