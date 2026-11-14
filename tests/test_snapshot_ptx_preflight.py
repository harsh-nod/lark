"""All 48 existing PTX header forgeries retain their exact refusal gates."""

from collections import ChainMap
from collections.abc import Mapping
from contextlib import ExitStack
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

from reproduction.paper_results import (
    ptx_dot_evidence, ptx_extended_evidence, ptx_matrix_evidence,
    ptx_pointwise_evidence, ptx_rotary_evidence, ptx_rotary_release,
    replay_snapshot as replay,
)
from reproduction.paper_results.check_snapshot_controls import (
    BMM_CONTROLS, GEMM_CONTROLS, GEMV_CONTROLS, LINEAR_CONTROLS, PTX_CONTROLS, ROTARY_CONTROLS,
    mutate_bmm_evidence, mutate_gemm_evidence, mutate_gemv_evidence,
    mutate_linear_evidence, mutate_ptx_evidence, mutate_rotary_evidence,
)

ROOT = Path(__file__).resolve().parents[1]
MODULES = {module.__name__.rsplit(".", 1)[-1]: module for module in (
    ptx_pointwise_evidence, ptx_dot_evidence, ptx_matrix_evidence,
    ptx_extended_evidence, ptx_rotary_evidence, ptx_rotary_release,
)}


class ActualFiles(Mapping):
    """Read actual producer inputs on demand; retain no file bytes or digests."""

    def __init__(self, names):
        self.names = set(names)

    def __iter__(self):
        return iter(self.names)

    def __len__(self):
        return len(self.names)

    def __getitem__(self, name):
        if name not in self.names:
            raise KeyError(name)
        return (ROOT / name).read_bytes()


class PtxPreflightTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.config = json.loads((ROOT / "reproduction/paper_results/snapshots/20261113-v27/targets.json").read_text())
        cls.inputs = ActualFiles(n for group in cls.config["evidence_groups"].values() for n in group)
        cls.script = ROOT / "reproduction/paper_results/audit.py"

    def check_overlay(self, entries):
        with ExitStack() as stack:
            stack.enter_context(patch.dict(sys.modules, MODULES))
            stack.enter_context(patch.object(replay, "frozen_header", side_effect=lambda root, name: json.loads(entries[name])))
            for module in (ptx_extended_evidence, ptx_rotary_evidence):
                original = module.Recording

                class Overlay(original):
                    def content(self, name):
                        relative = (self.root / name).relative_to(ROOT).as_posix()
                        return entries.maps[0][relative] if relative in entries.maps[0] else super().content(name)

                stack.enter_context(patch.object(module, "Recording", Overlay))
            return replay.preflight_frozen_ptx(self.script, self.config)

    def test_actual_six_kernel_headers_are_consistent(self):
        self.assertIsNone(self.check_overlay(ChainMap({}, self.inputs)))

    def test_all_existing_coherently_rehashed_control_claims_retain_their_gates(self):
        for kind, controls, mutate in (
            ("pointwise", PTX_CONTROLS, mutate_ptx_evidence),
            ("dot", GEMV_CONTROLS, mutate_gemv_evidence),
            ("matrix", GEMM_CONTROLS, mutate_gemm_evidence),
            ("bmm", BMM_CONTROLS, mutate_bmm_evidence),
            ("linear", LINEAR_CONTROLS, mutate_linear_evidence),
            ("rotary", ROTARY_CONTROLS, mutate_rotary_evidence),
        ):
            for name, gate in controls:
                with self.subTest(name=name):
                    entries = ChainMap({}, self.inputs)
                    mutate(entries, self.config, name)
                    with self.assertRaisesRegex(ValueError, "PTX " + kind + " " + gate):
                        self.check_overlay(entries)


if __name__ == "__main__":
    unittest.main()
