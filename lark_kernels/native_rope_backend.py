"""Source-checked Std proof imports for the closed native rotary profile."""

import errno
import json
import os
from pathlib import Path
import signal
import subprocess
import tempfile
import uuid

from .certificate import TOOLCHAIN, digest
from .ir import Refusal

PROJECT = '''name = "lark_native_rope_certificate"
version = "0.1.0"
defaultTargets = ["Main"]

[[lean_lib]]
name = "Lark"

[[lean_lib]]
name = "Main"
'''
TARGET = "Lark.NativeRopeCorrect"


def configuration():
    return {"lean-toolchain": TOOLCHAIN.encode(), "lakefile.toml": PROJECT.encode()}


def valid_cache(path, sources, key):
    try:
        marker = json.loads((path / "checked-build.json").read_text())
        if marker["key"] != key or any((path / n).read_bytes() != v for n, v in sources.items()):
            return False
        expected = {".lake/build/lib/lean/" + name[:-5] + ".olean" for name in sources if name.endswith(".lean")}
        return set(marker["compiled"]) == expected and all(digest((path / n).read_bytes()) == h
                                                           for n, h in marker["compiled"].items())
    except (OSError, ValueError, KeyError, TypeError):
        return False


def owned_build(command, cwd, env, timeout):
    process = subprocess.Popen(command, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, start_new_session=True)
    try:
        log, _ = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        log, _ = process.communicate()
        raise Refusal("proof-build", log + "\nPinned native proof-library build timed out")
    if process.returncode or "error:" in log or "sorryAx" in log:
        raise Refusal("proof-build", log)
    return log


def prepare(libraries, lean, timeout):
    lake = Path(lean).with_name("lake")
    if not lake.is_file():
        raise Refusal("toolchain", "Lake beside the verified Lean binary is required")
    version = subprocess.check_output([str(lake), "--version"], text=True, timeout=30)
    if "Lean version 4.19.0" not in version:
        raise Refusal("toolchain", "Lake must use Lean4.19.0")
    sources = {**libraries, **configuration()}
    identity = {"sources": {n: digest(v) for n, v in sorted(sources.items())}, "lake": version, "target": TARGET}
    key = digest(json.dumps(identity, sort_keys=True).encode())
    root = Path(os.environ.get("LARK_NATIVE_ROPE_CACHE", Path(tempfile.gettempdir()) / "lark-native-rope-proofs"))
    root.mkdir(parents=True, exist_ok=True)
    cache = root / key
    env = dict(os.environ)
    env.pop("LEAN_PATH", None)
    if not valid_cache(cache, sources, key):
        if cache.exists():
            cache.rename(root / (key + ".stale-" + uuid.uuid4().hex))
        with tempfile.TemporaryDirectory(prefix="building-", dir=root) as temporary:
            work = Path(temporary)
            for name, content in sources.items():
                dest = work / name
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(content)
            log = owned_build([str(lake), "build", TARGET], work, env, timeout)
            (work / "build.log").write_text(log)
            compiled = {".lake/build/lib/lean/" + name[:-5] + ".olean":
                        digest((work / (".lake/build/lib/lean/" + name[:-5] + ".olean")).read_bytes())
                        for name in sources if name.endswith(".lean")}
            (work / "checked-build.json").write_text(json.dumps({"key": key, "compiled": compiled}, indent=2) + "\n")
            try:
                work.rename(cache)
            except OSError as error:
                if error.errno not in (errno.EEXIST, errno.ENOTEMPTY) or not valid_cache(cache, sources, key):
                    raise Refusal("integrity", "concurrent native proof cache differs")
    if not valid_cache(cache, sources, key):
        raise Refusal("integrity", "pinned native proof cache differs")
    env["LEAN_PATH"] = str(cache / ".lake/build/lib/lean")
    return cache, env
