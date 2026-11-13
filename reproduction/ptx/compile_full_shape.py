"""Compile the frozen full-size CUDA fixtures to PTX on CPU, without proving them.

NVRTC/ptxas success is assembly evidence only. The separate reader probe does
not change the bounded PTX frontend, task capacities, or any proof statement.
"""

import argparse
import ctypes
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels.frontend import translate  # noqa: E402
from lark_kernels.ir import Buffer, Refusal, Task  # noqa: E402
from reproduction.local_models import full_shape_run as frozen  # noqa: E402

WHEELS = {
    "nvidia-cuda-nvrtc-cu12": (
        "12.9.86", "210cf05005a447e29214e9ce50851e83fc5f4358df8b453155d5e1918094dcb4"),
    "nvidia-cuda-runtime-cu12": (
        "12.9.79", "25bba2dfb01d48a9b59ca474a1ac43c6ebf7011f1b0b8cc44f54eb6ac48a96c3"),
    "nvidia-cuda-cccl-cu12": (
        "12.9.27", "37869e17ce2e1ecec6eddf1927cca0f8c34e64fd848d40453df559091e2d7117"),
}
PTXAS_SHA256 = "983b0e9283855979f42cebfd80d43f9b6e786eb84f03f7570bf941c4d3a3c461"
OPTIONS = ["--gpu-architecture=compute_80", "--std=c++17", "--fmad=false",
           "--ftz=false", "--prec-div=true", "--prec-sqrt=true"]
SCOPE = (
    "CPU-only compilation/assembly of the existing independent full-size CUDA sources. "
    "Original source, reference and task bytes, shapes, dtypes, launch and fuel are retained. "
    "Generated PTX has no source-bound LARK certificate, formal compiler-refinement proof, "
    "NVIDIA execution, numerical conformance or timing claim. No model calls or Lean runs. "
    "The reader-only probe constructs task attributes directly, without claiming bounded "
    "Task.parse acceptance or capacity validation; its outcome is not a proof result."
)


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n")


def verify_toolchain(root):
    downloads = read(root / "downloads.json")
    require(len(downloads) == len(WHEELS)
            and {row["package"] for row in downloads} == set(WHEELS),
            "Exactly the three pinned compiler/header wheels are required")
    bindings = {}
    for row in downloads:
        version, expected = WHEELS[row["package"]]
        require(row["status"] == "downloaded-and-hash-verified"
                and row["version"] == version and row["sha256"] == expected
                and Path(row["filename"]).name == row["filename"], "Compiler pin differs")
        wheel = root / row["filename"]
        require(digest(wheel.read_bytes()) == expected, "Changed compiler wheel")
        with zipfile.ZipFile(wheel) as archive:
            for name in archive.namelist():
                if not name.startswith("nvidia/") or name.endswith("/"):
                    continue
                require(".." not in Path(name).parts, "Unsafe wheel member")
                expected_file = digest(archive.read(name))
                require(name not in bindings or bindings[name] == expected_file,
                        "Conflicting compiler wheel members")
                path = root / "packages" / name
                require(path.is_file() and not path.is_symlink()
                        and digest(path.read_bytes()) == expected_file,
                        "Changed extracted compiler/header file: " + name)
                bindings[name] = expected_file
    return downloads, dict(sorted(bindings.items()))


def compile_one(specification):
    """Run only in a bounded child; loading NVRTC never loads a CUDA GPU driver."""
    spec = read(specification)
    lib = ctypes.CDLL(spec["nvrtc"])
    pointer = ctypes.POINTER
    api = {
        "nvrtcVersion": [pointer(ctypes.c_int), pointer(ctypes.c_int)],
        "nvrtcCreateProgram": [pointer(ctypes.c_void_p), ctypes.c_char_p, ctypes.c_char_p,
                               ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p],
        "nvrtcCompileProgram": [ctypes.c_void_p, ctypes.c_int, pointer(ctypes.c_char_p)],
        "nvrtcGetProgramLogSize": [ctypes.c_void_p, pointer(ctypes.c_size_t)],
        "nvrtcGetProgramLog": [ctypes.c_void_p, ctypes.c_void_p],
        "nvrtcGetPTXSize": [ctypes.c_void_p, pointer(ctypes.c_size_t)],
        "nvrtcGetPTX": [ctypes.c_void_p, ctypes.c_void_p],
        "nvrtcDestroyProgram": [pointer(ctypes.c_void_p)],
    }
    for name, arguments in api.items():
        function = getattr(lib, name)
        function.argtypes, function.restype = arguments, ctypes.c_int
    major, minor = ctypes.c_int(), ctypes.c_int()
    require(lib.nvrtcVersion(ctypes.byref(major), ctypes.byref(minor)) == 0
            and (major.value, minor.value) == (12, 9), "NVRTC version differs")
    source = Path(spec["input"]).read_bytes()
    require(digest(source) == spec["input_sha256"], "Changed compiler input")
    program = ctypes.c_void_p()
    require(lib.nvrtcCreateProgram(ctypes.byref(program), source, b"compile.cu",
                                   0, None, None) == 0, "nvrtcCreateProgram failed")
    try:
        options = (ctypes.c_char_p * len(spec["options"]))(
            *(item.encode() for item in spec["options"]))
        code = lib.nvrtcCompileProgram(program, len(options), options)
        size = ctypes.c_size_t()
        require(lib.nvrtcGetProgramLogSize(program, ctypes.byref(size)) == 0, "No NVRTC log")
        buffer = ctypes.create_string_buffer(size.value)
        require(lib.nvrtcGetProgramLog(program, buffer) == 0, "Cannot read NVRTC log")
        Path(spec["log"]).write_bytes(buffer.value)
        if code == 0:
            require(lib.nvrtcGetPTXSize(program, ctypes.byref(size)) == 0, "No PTX size")
            buffer = ctypes.create_string_buffer(size.value)
            require(lib.nvrtcGetPTX(program, buffer) == 0, "Cannot read PTX")
            Path(spec["ptx"]).write_bytes(buffer.value)
        return code
    finally:
        require(lib.nvrtcDestroyProgram(ctypes.byref(program)) == 0, "Cannot destroy NVRTC program")


def reader_probe(source, raw_task):
    # This is deliberately a reader probe, not admission to a certificate
    # profile: Task.parse's bounded capacities remain unchanged.
    task = Task(raw_task["name"], raw_task["entry"], "ptx",
                tuple(Buffer(b["name"], b["role"], tuple(b["shape"]), b["dtype"])
                      for b in raw_task["buffers"]),
                raw_task["launch"]["grid"], raw_task["launch"]["block"],
                raw_task["launch"]["warp"], tuple(raw_task["fuel"]))
    try:
        result = translate(source, task)
    except Refusal as error:
        return {"status": "reader-refused", "code": error.code, "detail": error.detail,
                "certificate_profile_validated": False, "formal_proof": False}
    return {"status": "reader-translated-only", "lowered_instructions": len(result.program),
            "certificate_profile_validated": False, "formal_proof": False}


def prepare(args):
    frozen.verify_preparation(args.prepared)
    require(frozen.sha(args.prepared / "manifest.json") == frozen.CUDA_PREPARATION_SHA256,
            "The frozen CUDA preparation is required")
    downloads, toolchain = verify_toolchain(args.toolchain)
    require(frozen.sha(args.ptxas) == PTXAS_SHA256, "Pinned ptxas 12.9.86 required")
    output = args.output.resolve()
    require(not output.exists() and not any((p / ".git").exists()
            for p in (output, *output.parents)), "Fresh output outside Git required")
    output.mkdir(parents=True)
    write(output / "toolchain-files.json", toolchain)
    write(output / "downloads.json", downloads)
    for row in downloads:
        name = row["package"] + "-metadata.json"
        content = (args.toolchain / name).read_bytes()
        require(digest(content) == row["metadata_sha256"], "Changed wheel metadata")
        (output / name).write_bytes(content)
    reader_sources = {}
    for name in ("lark_kernels/frontend.py", "lark_kernels/ptx.py", "lark_kernels/ir.py",
                 "reproduction/local_models/full_shape_run.py",
                 "reproduction/ptx/compile_full_shape.py"):
        content = (ROOT / name).read_bytes()
        target = output / "driver-sources" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(content)
        reader_sources[name] = digest(content)
    version = subprocess.check_output([str(args.ptxas), "--version"], timeout=30, text=True)
    packages = args.toolchain / "packages/nvidia"
    report = {
        "schema": 1, "status": "compiling", "scope": SCOPE,
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "driver_sha256": digest(Path(__file__).read_bytes()),
        "driver_sources": reader_sources,
        "preparation_manifest_sha256": frozen.CUDA_PREPARATION_SHA256,
        "preparation_source_manifest_sha256": frozen.sha(args.prepared / "source-manifest.json"),
        "toolchain_files_sha256": frozen.sha(output / "toolchain-files.json"),
        "ptxas": {"sha256": PTXAS_SHA256, "version": version},
        "compiler_options": OPTIONS, "per_process_timeout_seconds": 180,
        "original_paper_fully_reproduced": False, "nvidia_execution": False,
        "new_registered_source_certificates": 0, "model_calls": 0,
        "lean_checks": 0, "gpu_trials": 0, "cases": [],
    }
    write(output / "results.json", report)
    for case in frozen.TARGETS:
        request = read(args.prepared / "cases" / case / "request.json")
        destination = output / "cases" / case
        destination.mkdir(parents=True)
        (destination / "fixed-request.json").write_bytes(
            (args.prepared / "cases" / case / "request.json").read_bytes())
        sources = request["source_files"]
        row = {"case": case, "request_sha256": frozen.sha(destination / "fixed-request.json"),
               "source_bindings": {}, "stages": []}
        for name, content in sources.items():
            path = Path(name)
            target = destination / "original" / path.name
            require(not target.exists(), "Ambiguous fixture filename")
            target.parent.mkdir(exist_ok=True)
            target.write_bytes(content.encode())
            row["source_bindings"][name] = digest(content.encode())
        for name, content in sorted(sources.items()):
            path = Path(name)
            if path.suffix != ".cu":
                continue
            task_name = "task.json" if path.stem == "kernel" else path.stem + "-task.json"
            task = json.loads(sources[str(path.with_name(task_name))])
            stage = destination / path.stem
            stage.mkdir()
            wrapper = b"#include <cuda_fp16.h>\n" + content.encode()
            (stage / "compile.cu").write_bytes(wrapper)
            spec = {"nvrtc": str(packages / "cuda_nvrtc/lib/libnvrtc.so.12"),
                    "input": str(stage / "compile.cu"), "input_sha256": digest(wrapper),
                    "log": str(stage / "nvrtc.log"), "ptx": str(stage / "kernel.ptx"),
                    "options": OPTIONS + ["--include-path=" + str(packages / p)
                                          for p in ("cuda_runtime/include", "cuda_cccl/include")]}
            write(stage / "compiler-input.json", spec)
            start = time.monotonic()
            command = [sys.executable, str(Path(__file__).resolve()), "_compile-one",
                       str(stage / "compiler-input.json")]
            run = subprocess.run(command, capture_output=True, timeout=180)
            (stage / "compiler-child.stdout").write_bytes(run.stdout)
            (stage / "compiler-child.stderr").write_bytes(run.stderr)
            result = {"source_path": name, "task_path": str(path.with_name(task_name)),
                      "task": task, "compile_return_code": run.returncode,
                      "compile_seconds": time.monotonic() - start,
                      "compiler_command": command, "wrapper_sha256": digest(wrapper)}
            if run.returncode == 0:
                source = (stage / "kernel.ptx").read_text()
                entries = re.findall(r"\.visible\s+\.entry\s+(\w+)\s*\(", source)
                require(entries == [task["entry"]], "Generated entry differs from original task")
                command = [str(args.ptxas), "-arch=sm_80", "-o", str(stage / "kernel.cubin"),
                           str(stage / "kernel.ptx")]
                assembled = subprocess.run(command, capture_output=True, timeout=180)
                (stage / "ptxas.stdout").write_bytes(assembled.stdout)
                (stage / "ptxas.stderr").write_bytes(assembled.stderr)
                result.update(ptx_sha256=digest(source.encode()), ptx_bytes=len(source.encode()),
                              assembly_command=command, assembly_return_code=assembled.returncode,
                              reader_probe=reader_probe(source, task))
            row["stages"].append(result)
            write(stage / "results.json", result)
        report["cases"].append(row)
        write(output / "results.json", report)
        print(json.dumps({"case": case, "stages": len(row["stages"]),
                          "compiled": sum(s["compile_return_code"] == 0 for s in row["stages"]),
                          "assembled": sum(s.get("assembly_return_code") == 0
                                           for s in row["stages"])}), flush=True)
    stages = [stage for row in report["cases"] for stage in row["stages"]]
    complete = all(s["compile_return_code"] == s.get("assembly_return_code") == 0 for s in stages)
    report.update(status="full-size-PTX-compiled-and-assembled-only" if complete else
                  "full-size-PTX-compilation-failures-retained", cases_count=len(report["cases"]),
                  stages_count=len(stages), compiled_stages=sum(s["compile_return_code"] == 0
                                                               for s in stages),
                  assembled_stages=sum(s.get("assembly_return_code") == 0 for s in stages),
                  reader_refused_stages=sum(s.get("reader_probe", {}).get("status")
                                            == "reader-refused" for s in stages))
    write(output / "results.json", report)
    write(output / "manifest.json", {str(p.relative_to(output)): frozen.sha(p)
                                     for p in sorted(output.rglob("*")) if p.is_file()})
    require(complete, "Compilation failures retained; no automatic retry")


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "_compile-one":
        sys.exit(compile_one(Path(sys.argv[2])))
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepared", required=True, type=Path)
    parser.add_argument("--toolchain", required=True, type=Path)
    parser.add_argument("--ptxas", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    args = parser.parse_args()
    for name in ("prepared", "toolchain", "ptxas", "output"):
        setattr(args, name, getattr(args, name).resolve())
    prepare(args)


if __name__ == "__main__":
    main()
