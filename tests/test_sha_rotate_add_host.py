"""The host wrapper keeps its receipts away from the container and packages results without following links."""
import base64, gzip, json, os, pathlib, subprocess, sys, tempfile, unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
HOST = (ROOT / 'experiments/sha-rotate-add/host-full.sh').read_text()


def packaging_code():
    return HOST.split("python3 - \"$results\" \"$output\" <<'PY'\n", 1)[1].split('\nPY\n', 1)[0]


class PackagingTests(unittest.TestCase):
    def package(self, prepare):
        with tempfile.TemporaryDirectory() as directory:
            base = pathlib.Path(directory); root = base / 'results'; output = base / 'output'; root.mkdir(); output.mkdir()
            (root / 'gate.log').write_text('log'); (root / 'exit-code.txt').write_text('0\n')
            (output / 'result.json').write_text('{"status": "completed"}')
            prepare(root, output, base)
            done = subprocess.run([sys.executable, '-c', packaging_code(), str(root), str(output)], capture_output=True, text=True, timeout=30)
            packed = (root / 'public-result.b64').read_bytes() if (root / 'public-result.b64').exists() else None
            return done, (json.loads(gzip.decompress(base64.b64decode(packed))) if packed else None)

    def test_host_receipts_and_the_container_result_are_packaged(self):
        done, packed = self.package(lambda root, output, base: None)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(packed, {'exit-code.txt': '0\n', 'gate.log': 'log', 'result.json': '{"status": "completed"}'})
        self.assertIn('QSB_PUBLIC_RESULT_META=', done.stdout)

    def test_container_is_not_given_the_host_receipt_directory(self):
        self.assertIn('--mount type=bind,src="$output",dst=/results', HOST)
        self.assertNotIn('src="$results"', HOST)
        for receipt in ('deadline.txt', 'pull.log', 'gpu.txt', 'gate.log', 'exit-code.txt'):
            self.assertIn('"$results/' + receipt + '"', HOST)

    def test_other_container_output_cannot_replace_host_receipts(self):
        def forge(root, output, base):
            (output / 'gate.log').write_text('forged log'); (output / 'exit-code.txt').write_text('0\n'); (output / 'gpu.txt').write_text('forged')
        done, packed = self.package(forge)
        self.assertEqual(done.returncode, 0, done.stderr)
        self.assertEqual(packed['gate.log'], 'log'); self.assertNotIn('gpu.txt', packed)

    def test_missing_container_result_is_packaged_without_it(self):
        done, packed = self.package(lambda root, output, base: (output / 'result.json').unlink())
        self.assertEqual(done.returncode, 0, done.stderr); self.assertNotIn('result.json', packed)

    def test_links_and_other_entries_are_refused_without_reading_the_target(self):
        def secret(base): (base / 'host-secret').write_text('must not leave the host'); return base / 'host-secret'
        def result_link(root, output, base): (output / 'result.json').unlink(); os.symlink(secret(base), output / 'result.json')
        def receipt_link(root, output, base): os.symlink(secret(base), root / 'leak.txt')
        def directory(root, output, base): (root / 'nested').mkdir()
        def fifo(root, output, base): os.mkfifo(root / 'pipe')
        for prepare in (result_link, receipt_link, directory, fifo):
            with self.subTest(prepare=prepare.__name__):
                done, packed = self.package(prepare)
                self.assertNotEqual(done.returncode, 0)
                self.assertIn('non-regular result entry', done.stderr)
                self.assertIsNone(packed)
                self.assertNotIn('must not leave the host', done.stdout + done.stderr)

    def test_aggregate_size_and_entry_count_are_enforced_while_reading(self):
        def many_large(root, output, base):
            for i in range(4): (root / f'big{i}.log').write_bytes(b'a' * 3000000)
        def many_small(root, output, base):
            for i in range(40): (root / f'small{i}.log').write_text('x')
        def large_result(root, output, base): (output / 'result.json').write_bytes(b'a' * 9000000)
        for prepare, message in ((many_large, 'result too large'), (many_small, 'too many result entries'), (large_result, 'result too large')):
            with self.subTest(prepare=prepare.__name__):
                done, packed = self.package(prepare)
                self.assertNotEqual(done.returncode, 0); self.assertIn(message, done.stderr); self.assertIsNone(packed)

    def test_oversized_encoded_result_is_refused(self):
        def big(root, output, base): (root / 'gate.log').write_bytes(os.urandom(500000).hex().encode())
        done, packed = self.package(big)
        self.assertNotEqual(done.returncode, 0); self.assertIn('encoded result too large', done.stderr); self.assertIsNone(packed)


if __name__ == '__main__':
    unittest.main()
