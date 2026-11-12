"""Run frozen native AWQ sources; audit numerical output separately on the CPU."""

import argparse
import ctypes as C
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import socket
import subprocess
import tarfile
import time


def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024*1024), b''):
            h.update(data)
    return h.hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data, out = args.input.resolve(), args.output.resolve()
    for name, expected in json.loads((data/'manifest.json').read_text())['files'].items():
        path = (data/name).resolve()
        if not path.is_relative_to(data) or sha(path) != expected:
            raise ValueError('Frozen input differs: '+name)
    out.mkdir(parents=True, exist_ok=False)
    command = ['hipcc', '-O2', '-std=c++17', '-shared', '-fPIC', '-ffp-contract=off',
               '--offload-arch=gfx950', '-MD', '-MF', str(out/'dependencies.d'),
               str(data/'driver.hip'), '-o', str(out/'driver.so')]
    built = subprocess.run(command, capture_output=True, text=True, timeout=180)
    (out/'build.log').write_text(built.stdout+built.stderr)
    if built.returncode:
        raise RuntimeError('Compile failed: '+built.stderr[-4000:])
    paths = shlex.split((out/'dependencies.d').read_text().replace('\\\n', ' ').split(':', 1)[1])
    headers = {str(Path(p).resolve()): sha(Path(p).resolve()) for p in paths}
    (out/'compiler-inputs.json').write_text(json.dumps(headers, indent=2)+'\n')
    with tarfile.open(out/'compiler-inputs.tar.gz', 'w:gz') as archive:
        for name in sorted(headers):
            archive.add(name, arcname=name.lstrip('/'), recursive=False)
    hip = C.CDLL('/opt/rocm/lib/libamdhip64.so')
    hip.hipGetErrorString.argtypes, hip.hipGetErrorString.restype = [C.c_int], C.c_char_p
    hip.hipMemGetInfo.argtypes = [C.POINTER(C.c_size_t), C.POINTER(C.c_size_t)]
    hip.hipMalloc.argtypes = [C.POINTER(C.c_void_p), C.c_size_t]
    hip.hipMemcpy.argtypes = [C.c_void_p, C.c_void_p, C.c_size_t, C.c_int]
    hip.hipFree.argtypes = [C.c_void_p]
    hip.hipDeviceGetName.argtypes = [C.c_char_p, C.c_int, C.c_int]
    hip.hipDeviceGetPCIBusId.argtypes = [C.c_char_p, C.c_int, C.c_int]

    def checked(code):
        if code:
            raise RuntimeError(hip.hipGetErrorString(code).decode())

    checked(hip.hipSetDevice(0))
    free, total = C.c_size_t(), C.c_size_t()
    checked(hip.hipMemGetInfo(C.byref(free), C.byref(total)))
    bus = C.create_string_buffer(64)
    checked(hip.hipDeviceGetPCIBusId(bus, len(bus), 0))
    pci = bus.value.decode().lower()
    matching = [p/'gpu_busy_percent' for p in Path('/sys/class/drm').glob('card[0-9]*/device')
                if p.resolve().name.lower() == pci and (p/'gpu_busy_percent').is_file()]
    if len(matching) != 1:
        raise RuntimeError('Cannot bind selected GPU to an idle-state probe; no launch executed')
    # HIP context creation can itself appear in the immediately following
    # utilisation sample. Require three idle samples after initialisation;
    # never accept a nonzero final sample or reduce the free-memory threshold.
    samples, consecutive = [], 0
    for attempt in range(20):
        checked(hip.hipMemGetInfo(C.byref(free), C.byref(total)))
        sample = {'free_bytes': free.value, 'total_bytes': total.value,
                  'busy_percent': int(matching[0].read_text().strip())}
        samples.append(sample)
        consecutive = consecutive+1 if sample['busy_percent'] == 0 and free.value >= .98*total.value else 0
        if consecutive == 3:
            break
        if attempt < 19:
            time.sleep(.5)
    memory = {**samples[-1], 'minimum_free_fraction': .98,
              'pci_bus_id': pci, 'idle_probe': str(matching[0]),
              'minimum_idle_samples': 3, 'poll_interval_seconds': .5,
              'max_samples': 20, 'samples': samples}
    (out/'memory-guard.json').write_text(json.dumps(memory, indent=2)+'\n')
    if consecutive != 3:
        raise RuntimeError('Selected GPU is occupied; no launch executed')
    lib = C.CDLL(str(out/'driver.so'))
    lib.run_case.argtypes, lib.run_case.restype = [C.c_int]+[C.c_void_p]*3, C.c_int
    lib.runtime_attribute.argtypes, lib.runtime_attribute.restype = [C.c_int], C.c_int
    lib.runtime_architecture.restype = C.c_char_p
    attributes = [lib.runtime_attribute(i) for i in range(3)]
    architecture = lib.runtime_architecture().decode()
    if attributes[0] != 64 or attributes[1] < 64 or attributes[2] < 9984 or not architecture.startswith('gfx950'):
        raise ValueError('Native wave64/gfx950 geometry unavailable')
    device = C.create_string_buffer(256)
    checked(hip.hipDeviceGetName(device, len(device), 0))
    metadata = json.loads((data/'dataset.json').read_text())
    guard, records = b'\x5a'*128, []
    for case in metadata['cases']:
        for trial in case['trials']:
            stem, m, k, n = trial['stem'], case['m'], case['k'], case['n']
            a, b = (data/(stem+'-a.bin')).read_bytes(), (data/(stem+'-b.bin')).read_bytes()
            if len(a) != m*k*2 or len(b) != k*n*2:
                raise ValueError('Truncated operand')
            initial = (a, b, b'\x00\x7e'*(m*n))
            pointers = []
            try:
                for raw in initial:
                    ptr = C.c_void_p()
                    checked(hip.hipMalloc(C.byref(ptr), len(raw)+256))
                    pointers.append(ptr)
                    host = C.create_string_buffer(guard+raw+guard)
                    checked(hip.hipMemcpy(ptr, host, len(raw)+256, 1))
                checked(lib.run_case(case['index'], *(C.c_void_p(p.value+128) for p in pointers)))
                checked(hip.hipDeviceSynchronize())
                actual = []
                for i, (ptr, raw) in enumerate(zip(pointers, initial)):
                    host = C.create_string_buffer(len(raw)+256)
                    checked(hip.hipMemcpy(host, ptr, len(raw)+256, 2))
                    got = host.raw
                    if got[:128] != guard or got[-128:] != guard:
                        raise RuntimeError('Allocation guard changed')
                    got = got[128:-128]
                    if i < 2 and got != raw:
                        raise RuntimeError('Read-only matrix changed')
                    actual.append(got)
                (out/(stem+'-out.bin')).write_bytes(actual[2])
                records.append({'case': case['index'], 'trial': trial['trial'], 'stem': stem,
                                'output_elements': m*n, 'all_allocation_guards_unchanged': True,
                                'a_unchanged': True, 'b_unchanged': True,
                                'source_sha256': case['source_sha256'],
                                'output_sha256': sha(out/(stem+'-out.bin'))})
                print(json.dumps({'case': case['index'], 'trial': trial['trial'],
                                  'status': 'runtime-checks-passed'}), flush=True)
            finally:
                for ptr in pointers:
                    checked(hip.hipFree(ptr))
    report = {'schema': 1, 'status': 'runtime-checks-passed-pending-independent-numerical-audit',
              'recorded_at_utc': datetime.now(timezone.utc).isoformat(), 'hostname': socket.gethostname(),
              'device': device.value.decode(), 'architecture': architecture, 'warp': attributes[0],
              'block': 64, 'method': metadata['method'], 'trials': len(records), 'launches': len(records),
              'output_elements': sum(r['output_elements'] for r in records), 'cases': records,
              'input_manifest_sha256': sha(data/'manifest.json'), 'runner_sha256': sha(Path(__file__)),
              'binary_sha256': sha(out/'driver.so'), 'compile_command': command,
              'compiler': subprocess.check_output(['hipcc', '--version'], text=True),
              'compiler_inputs': len(headers), 'source_certificates': 0, 'model_calls': 0,
              'whole_kernel_execution_proved': False, 'actual_whole_trace_race_freedom_proved': False,
              'source_reference_equality_proved': False, 'ieee_equivalence_proved': False,
              'original_nvidia_kernel_executed': False, 'original_paper_fully_reproduced': False}
    (out/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    (out/'manifest.json').write_text(json.dumps({p.relative_to(out).as_posix(): sha(p)
                                               for p in sorted(out.rglob('*')) if p.is_file()}, indent=2)+'\n')
    print(json.dumps({key: report[key] for key in ('status', 'trials', 'launches', 'output_elements')}), flush=True)


if __name__ == '__main__':
    main()
