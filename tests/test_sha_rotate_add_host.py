"""The host wrapper's result packaging must not follow links out of the results directory."""
import base64, gzip, json, os, pathlib, subprocess, sys, tempfile, unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]


def packaging_code():
    text = (ROOT / 'experiments/sha-rotate-add/host-full.sh').read_text()
    return text.split("python3 - \"$results\" <<'PY'\n", 1)[1].split('\nPY\n', 1)[0]


class PackagingTests(unittest.TestCase):
    def package(self, prepare):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory) / 'results'; root.mkdir()
            (root / 'result.json').write_text('{"status": "completed"}'); (root / 'gate.log').write_text('log')
            prepare(root, pathlib.Path(directory))
            done = subprocess.run([sys.executable, '-c', packaging_code(), str(root)], capture_output=True, text=True, timeout=30)
            packed = (root / 'public-result.b64').read_bytes() if (root / 'public-result.b64').exists() else None
            return done, packed

    def test_regular_files_are_packaged(self):
        done, packed = self.package(lambda root, outside: None)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(json.loads(gzip.decompress(base64.b64decode(packed))), {'gate.log': 'log', 'result.json': '{"status": "completed"}'})
        self.assertIn('QSB_PUBLIC_RESULT_META=', done.stdout)

    def test_symlink_and_other_entries_are_refused_without_reading_the_target(self):
        def link(root, outside):
            (outside / 'host-secret').write_text('must not leave the host'); os.symlink(outside / 'host-secret', root / 'leak.txt')
        def directory(root, outside): (root / 'nested').mkdir()
        def fifo(root, outside): os.mkfifo(root / 'pipe')
        for prepare in (link, directory, fifo):
            with self.subTest(prepare=prepare.__name__):
                done, packed = self.package(prepare)
                self.assertNotEqual(done.returncode, 0)
                self.assertIn('non-regular result entry', done.stderr)
                self.assertIsNone(packed)
                self.assertNotIn('must not leave the host', done.stdout + done.stderr)

    def test_aggregate_size_and_entry_count_are_enforced_while_reading(self):
        def many_large(root, outside):
            for i in range(4): (root / f'big{i}.log').write_bytes(b'a' * 3000000)
        def many_small(root, outside):
            for i in range(40): (root / f'small{i}.log').write_text('x')
        for prepare, message in ((many_large, 'result too large'), (many_small, 'too many result entries')):
            with self.subTest(prepare=prepare.__name__):
                done, packed = self.package(prepare)
                self.assertNotEqual(done.returncode, 0); self.assertIn(message, done.stderr); self.assertIsNone(packed)

    def test_oversized_result_is_refused(self):
        def big(root, outside): (root / 'gate.log').write_bytes(os.urandom(500000).hex().encode())
        done, packed = self.package(big)
        self.assertNotEqual(done.returncode, 0); self.assertIn('encoded result too large', done.stderr); self.assertIsNone(packed)


if __name__ == '__main__':
    unittest.main()
