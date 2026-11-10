"""Pinned optional Mathlib imports, isolated from certificate-supplied build files."""

import errno
import json
import os
from pathlib import Path
import signal
import subprocess
import sysconfig
import tempfile

from .certificate import TOOLCHAIN, digest
from .ir import Refusal

MATHLIB = "c44e0c8ee63ca166450922a373c7409c5d26b00b"
PROJECT = """name = "lark_real_certificate"
version = "0.1.0"
defaultTargets = ["Main"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "c44e0c8ee63ca166450922a373c7409c5d26b00b"

[[lean_lib]]
name = "Lark"

[[lean_lib]]
name = "LarkReal"

[[lean_lib]]
name = "Main"
"""


def resource(relative):
    root = Path(__file__).resolve().parents[1]
    path = root / relative
    if not path.is_file():
        path = Path(sysconfig.get_path("data")) / "share/lark" / relative
    if not path.is_file():
        raise Refusal("installation", "optional real proof resource is missing: " + relative)
    return path


def lock_bytes():
    lock = json.loads(resource("lean-real/lake-manifest.json").read_text())
    lock["packages"] = [p for p in lock["packages"] if p["type"] == "git"]
    lock["name"] = "lark_real_certificate"
    pins = [p for p in lock["packages"] if p["name"] == "mathlib"]
    if len(pins) != 1 or pins[0]["rev"] != MATHLIB or len(lock["packages"]) != 9:
        raise Refusal("installation", "unexpected optional dependency lock")
    return (json.dumps(lock, indent=2) + "\n").encode()


def configuration():
    return {
        "lakefile.toml": PROJECT.encode(),
        "lake-manifest.json": lock_bytes(),
        "lean-toolchain": TOOLCHAIN.encode(),
    }


def seed_project():
    selected = os.environ.get("LARK_REAL_PROJECT")
    if selected:
        return Path(selected).expanduser().resolve()
    return resource("lean-real/lake-manifest.json").parent


def dependencies():
    project = seed_project()
    result = {}
    for package in json.loads(lock_bytes())["packages"]:
        path = project / ".lake/packages" / package["name"]
        if not path.is_dir():
            raise Refusal(
                "real-dependencies",
                "initialize the optional lean-real package/cache first; "
                "LARK_REAL_PROJECT may select an initialized checkout",
            )
        head = subprocess.run(
            ["git", "rev-parse", "HEAD"], cwd=path, text=True, capture_output=True, timeout=30
        )
        clean = subprocess.run(
            ["git", "diff", "--quiet", "--no-ext-diff", "--no-textconv", "HEAD", "--"],
            cwd=path,
            capture_output=True,
            timeout=30,
        )
        if head.returncode or head.stdout.strip() != package["rev"] or clean.returncode:
            raise Refusal("integrity", "optional dependency source differs: " + package["name"])
        result[package["name"]] = path.resolve()
    return project, result


def owned_build(command, cwd, env, timeout):
    process = subprocess.Popen(
        command,
        cwd=cwd,
        env=env,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    try:
        log, _ = process.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        log, _ = process.communicate()
        raise Refusal("real-build", log + "\nOptional proof-library build timed out")
    if process.returncode or "error:" in log or "sorryAx" in log:
        raise Refusal("real-build", log)
    return log


def valid_cache(path, sources, key):
    try:
        marker = json.loads((path / "checked-build.json").read_text())
        if marker["key"] != key:
            return False
        if any((path / name).read_bytes() != content for name, content in sources.items()):
            return False
        expected = {
            ".lake/build/lib/lean/" + name[:-5] + ".olean"
            for name in sources
            if name.endswith(".lean")
        }
        if set(marker["compiled"]) != expected:
            return False
        return all(
            digest((path / name).read_bytes()) == h for name, h in marker["compiled"].items()
        )
    except (OSError, KeyError, ValueError, TypeError):
        return False


def prepare(libraries, lean, timeout, *, target="LarkReal.WaveSum"):
    """Compile pinned own libraries once, then return a source-checked import environment."""
    if target.replace(".", "/") + ".lean" not in libraries:
        raise Refusal("configuration", "optional proof target must be in the pinned source set")
    project, seeds = dependencies()
    lake = Path(lean).with_name("lake")
    if not lake.is_file():
        raise Refusal("toolchain", "Lake beside the verified Lean binary is required")
    version = subprocess.check_output([str(lake), "--version"], text=True, timeout=30)
    if "Lean version 4.19.0" not in version:
        raise Refusal("toolchain", "Lake must use Lean 4.19.0")
    sources = {**libraries, **configuration()}
    source_hashes = {name: digest(content) for name, content in sorted(sources.items())}
    identity = {"sources": source_hashes, "lake": version}
    if target != "LarkReal.WaveSum":
        identity["target"] = target
    key = digest(json.dumps(identity, sort_keys=True).encode())
    cache_root = project / ".lake/lark-real-proofs"
    cache_root.mkdir(parents=True, exist_ok=True)
    cache = cache_root / key
    task_env = dict(os.environ)
    task_env.pop("LEAN_PATH", None)
    if not valid_cache(cache, sources, key):
        if cache.exists():
            raise Refusal(
                "integrity", "managed proof cache changed; remove that cache directory and rebuild"
            )
        with tempfile.TemporaryDirectory(prefix=key[:12] + "-", dir=cache_root) as temporary:
            build = Path(temporary)
            for name, content in sources.items():
                source_path = build / name
                source_path.parent.mkdir(parents=True, exist_ok=True)
                source_path.write_bytes(content)
            packages = build / ".lake/packages"
            packages.mkdir(parents=True)
            for name, dependency_path in seeds.items():
                (packages / name).symlink_to(dependency_path, target_is_directory=True)
            log = owned_build(
                [str(lake), "-f", "lakefile.toml", "build", "+" + target],
                build,
                task_env,
                timeout,
            )
            (build / "build.log").write_text(log)
            compiled = {
                ".lake/build/lib/lean/" + name[:-5] + ".olean": digest(
                    (build / ".lake/build/lib/lean" / (name[:-5] + ".olean")).read_bytes()
                )
                for name in libraries
            }
            (build / "checked-build.json").write_text(
                json.dumps({"key": key, "sources": source_hashes, "compiled": compiled}, indent=2)
                + "\n"
            )
            try:
                build.rename(cache)
            except OSError as error:
                if error.errno not in {errno.EEXIST, errno.ENOTEMPTY}:
                    raise
                if not valid_cache(cache, sources, key):
                    raise Refusal("integrity", "concurrent managed proof cache differs") from error
    if not valid_cache(cache, sources, key):
        raise Refusal("integrity", "managed proof cache validation failed")
    # Resolve every path before invoking Lean from a different fresh directory.
    paths = [cache / ".lake/build/lib/lean"]
    paths += [p / ".lake/build/lib/lean" for p in seeds.values()]
    task_env["LEAN_PATH"] = os.pathsep.join(str(p.resolve()) for p in paths)
    return cache, task_env
