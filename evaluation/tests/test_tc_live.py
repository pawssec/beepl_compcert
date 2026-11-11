"""Failure-path checks for the privileged namespace runner, without privileges."""
import json
import pathlib
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / 'tools'))
import tc_live


class NamespaceCleanupTests(unittest.TestCase):
    def test_created_namespaces_removed_when_veth_setup_fails(self):
        calls = []
        def fake_command(args, allowed=(0,)):
            calls.append(args)
            if 'veth' in args:
                raise RuntimeError('simulated veth creation failure')
            return subprocess.CompletedProcess(args, 0, '', '')
        with tempfile.TemporaryDirectory() as directory, \
                patch.object(tc_live, 'HERE', pathlib.Path(directory)), \
                patch.object(tc_live.os, 'geteuid', return_value=0), \
                patch.object(tc_live.shutil, 'which', return_value='/fake/tool'), \
                patch.object(tc_live, 'prebuilt_program', return_value=pathlib.Path('/fake/object')), \
                patch.object(tc_live.signal, 'signal'), \
                patch.object(tc_live, 'command', side_effect=fake_command):
            self.assertEqual(tc_live.main(), 1)
            report = json.loads((pathlib.Path(directory) / 'results/tc-live.json').read_text())
        created = [args[-1] for args in calls if args[:3] == ['ip', 'netns', 'add']]
        deleted = [args[-1] for args in calls if args[:3] == ['ip', 'netns', 'del']]
        self.assertEqual(len(created), 2)
        link_add = next(args for args in calls if 'veth' in args)
        self.assertEqual(link_add[3:], ['link', 'add', 'name', 'tx', 'type',
                                        'veth', 'peer', 'name', 'rx'])
        for args in calls:
            if args[3:5] == ['link', 'set']:
                self.assertEqual(args[5], 'dev')
        self.assertEqual(deleted, list(reversed(created)))
        self.assertTrue(report['cleanup_complete'])
        self.assertFalse(report['passed'])


if __name__ == '__main__':
    unittest.main()
