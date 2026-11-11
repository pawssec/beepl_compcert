"""Check that counter assertions depend on map state, including CPU migration."""
import contextlib
import io
import pathlib
import sys
import unittest
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'tools'))
from map_eval import run_cases


class Counter:
    def __init__(self, increment=True):
        self.values = [0, 0, 0]
        self.calls = 0
        self.increment = increment

    def map_lookup(self, key):
        return self.values[:]

    def run(self, packet):
        if self.increment:
            self.values[self.calls % 3] += 1
        self.calls += 1
        return 2, packet, 1


class MapAssertionsTests(unittest.TestCase):
    def test_counter_sums_values_across_cpus(self):
        results = []
        with contextlib.redirect_stdout(io.StringIO()):
            run_cases(Counter(), 'xdp_map_counter', b'packet', results)
        self.assertEqual([t['map_total'] for t in results], [1, 2, 3, 4, 5])
        self.assertEqual(results[-1]['nonzero_cpu_values'], {'0': 2, '1': 2, '2': 1})
        self.assertTrue(all(t['passed'] for t in results))

    def test_passing_action_without_counter_update_fails(self):
        results = []
        with contextlib.redirect_stdout(io.StringIO()), self.assertRaises(AssertionError):
            run_cases(Counter(increment=False), 'xdp_map_counter', b'packet', results)
        self.assertFalse(results[0]['passed'])


if __name__ == '__main__':
    unittest.main()
