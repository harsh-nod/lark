"""Parse untrusted proof slots as complete terms without elaborating their code."""

import json
import os
from pathlib import Path
import re
import subprocess
import sysconfig
import tempfile

from .ir import Refusal


def source_path():
    relative = Path("lean/Lark/ProofSyntax.lean")
    repo = Path(__file__).resolve().parents[1] / relative
    installed = Path(sysconfig.get_path("data")) / "share/lark" / relative
    if repo.is_file():
        return repo
    if installed.is_file():
        return installed
    raise Refusal("installation", "Pinned proof-term parser is missing")


def check_terms(proofs, binary, timeout=180, *, env=None, imports=()):
    """Use Lean's term parser, including its end-of-input check, before execution.

    Proof strings are JSON data read by the trusted parser command. They are
    never interpolated into an executable Lean file during this check.
    The caller must still enforce its tactic policy and check actual proofs.
    """
    if (
        not isinstance(proofs, dict)
        or not 1 <= len(proofs) <= 16
        or any(not isinstance(p, str) or len(p) > 20000 for p in proofs.values())
    ):
        raise Refusal("proposal", "Expected bounded proof strings")
    if timeout <= 0:
        raise Refusal("configuration", "Positive proof-parser timeout required")
    for module in imports:
        if not isinstance(module, str) or not re.fullmatch(
            r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", module
        ):
            raise Refusal("configuration", "Unexpected proof-parser import")
    source = source_path().read_text()
    prefix = "import Lean\nimport Std\n"
    if not source.startswith(prefix):
        raise Refusal("installation", "Unexpected proof-parser header")
    source = prefix + "".join("import " + n + "\n" for n in imports) + source[len(prefix) :]
    with tempfile.TemporaryDirectory(prefix="lark-proof-terms-") as temporary:
        directory = Path(temporary)
        (directory / "ProofTerms.json").write_text(
            json.dumps([p.strip() for p in proofs.values()]) + "\n"
        )
        (directory / "Main.lean").write_text(source + "\nlark_check_proof_terms\n")
        try:
            run = subprocess.run(
                [str(binary), "Main.lean"],
                cwd=directory,
                env=env or os.environ,
                text=True,
                capture_output=True,
                timeout=min(timeout, 180),
            )
        except subprocess.TimeoutExpired:
            return False, "Proof-term parsing timed out; no candidate was elaborated.\n"
    log = run.stdout + run.stderr
    marker = "LARK_PROOF_TERMS_OK " + str(len(proofs))
    return run.returncode == 0 and "error:" not in log and marker in log, log
