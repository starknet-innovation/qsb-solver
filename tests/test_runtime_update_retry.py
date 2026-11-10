"""The runtime stages retry Ubuntu's package update; exercise that shell with stand-in commands."""
import os, pathlib, re, stat, subprocess, tempfile, unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
DOCKERFILES = {'worker/Dockerfile': 'python3 python3-pip libssl3', 'worker/optimized/Dockerfile': 'python3 libssl3'}
CLEANUP = ' && rm -rf /var/lib/apt/lists/*'


def update_command(path):
    text = (ROOT / path).read_text().replace('\\\n', ' ')
    commands = [line[4:] for line in text.splitlines() if line.startswith('RUN for attempt in 1 2 3; do')]
    if len(commands) != 1: raise AssertionError('expected one retried update step in ' + path)
    return commands[0]


class RetryTests(unittest.TestCase):
    def run_update(self, path, failures):
        command = update_command(path)
        self.assertTrue(command.endswith(CLEANUP))
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory); log = root / 'calls.log'
            # Stand-ins: apt-get fails its first `failures` update calls; sleep returns at once.
            (root / 'apt-get').write_text(f"""#!/bin/sh
echo "$*" >> {log}
case "$*" in *" update") n=$(grep -c ' update$' {log}); [ "$n" -gt {failures} ] || exit 100;; esac
exit 0
""")
            (root / 'sleep').write_text('#!/bin/sh\nexit 0\n')
            for name in ('apt-get', 'sleep'): (root / name).chmod(stat.S_IRWXU)
            # The cache cleanup is checked above and replaced here: it must not touch the test host.
            done = subprocess.run(['sh', '-c', command[:-len(CLEANUP)] + ' && echo CLEANED'], capture_output=True, text=True,
                                  env={**os.environ, 'PATH': f"{root}{os.pathsep}{os.environ['PATH']}"}, timeout=20)
            return done, log.read_text().splitlines()

    def test_both_runtime_stages_retry_the_same_three_commands(self):
        for path, packages in DOCKERFILES.items():
            command = update_command(path)
            steps = re.findall(r'apt-get -o Dir::Etc::SourceParts=/nonexistent (update|upgrade -y|install -y --no-install-recommends [a-z0-9 -]+?)(?= +&&)', command)
            self.assertEqual(steps, ['update', 'upgrade -y', 'install -y --no-install-recommends ' + packages], path)
            self.assertEqual(command.count('apt-get '), 3)

    def test_succeeds_without_retry_when_the_mirror_is_consistent(self):
        for path in DOCKERFILES:
            done, calls = self.run_update(path, failures=0)
            self.assertEqual((done.returncode, done.stdout.strip(), len(calls)), (0, 'CLEANED', 3), path)

    def test_recovers_after_two_failed_updates(self):
        for path in DOCKERFILES:
            done, calls = self.run_update(path, failures=2)
            self.assertEqual((done.returncode, done.stdout.strip()), (0, 'CLEANED'), path)
            self.assertEqual(sum(c.endswith(' update') for c in calls), 3)
            self.assertEqual(len(calls), 5)

    def test_fails_after_three_attempts(self):
        for path in DOCKERFILES:
            done, calls = self.run_update(path, failures=3)
            self.assertNotEqual(done.returncode, 0, path)
            self.assertNotIn('CLEANED', done.stdout)
            self.assertEqual(len(calls), 3)


if __name__ == '__main__':
    unittest.main()
