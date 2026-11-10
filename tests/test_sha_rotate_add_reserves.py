"""The experiment's host gate and staging limits must fit inside the controller's send reserve."""
import pathlib, re, unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
EXP = ROOT / 'experiments/sha-rotate-add'


class ReserveTests(unittest.TestCase):
    def test_host_gate_and_staging_fit_the_send_reserve(self):
        send = int(re.search(r'MIN_SEND_SECONDS=(\d+)', (ROOT / 'ops/aws-gpu-execution/operate.py').read_text()).group(1))
        host = (EXP / 'host-full.sh').read_text()
        before, after = [int(x) for x in re.findall(r'-ge (\d+) \]', host)]
        self.assertEqual((before, after), (1500, 1200))
        limit = int(re.search(r"len\(data\)>(\d+):raise ValueError\('encoded result too large'\)", host).group(1))
        chunks = -(-limit // 18000)
        self.assertGreaterEqual(after, 720 + 60 + chunks * 8 + 120)  # gate, packaging, largest collection, collector reserve
        self.assertGreaterEqual(before, after + 300)                 # image pull limit
        stage = (EXP / 'stage_full.py').read_text()
        self.assertIn('--max-time 120', stage)
        self.assertIn('end=time.monotonic()+20;stream=urllib.request.urlopen(url,timeout=10)', stage)  # at most 30 s per file
        self.assertGreaterEqual(send, before + 120 + 11 * 30 + 180)  # archive, at most eleven runner files, readiness


if __name__ == '__main__':
    unittest.main()
