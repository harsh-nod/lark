"""Package completed exact-source PTX proof evidence; run no experiment."""

from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tarfile

ROOT = Path('/tmp/lark-ptx-matrix-proof-packet-v1-20261113')
REPO = Path('/tmp/lark-ptx-matrix-refinement-20261113')
PRODUCER = 'c1f6e9220c36df38152dd738fa812288bec64eb7'
SOURCES = {
    'export': Path('/tmp/lark-ptx-matrix-source-export-v2-20261113'),
    'replay': Path('/tmp/lark-ptx-matrix-source-replay-v1-20261113'),
    'controls': Path('/tmp/lark-ptx-matrix-source-controls-v1-20261113'),
    'installed-wheel': Path('/tmp/lark-ptx-matrix-wheel-validation-v2-20261113'),
    'wheel-build': Path('/tmp/lark-ptx-matrix-wheel-v1-20261113'),
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def inventory(root):
    require(not any(p.is_symlink() for p in root.rglob('*')), 'Symlink in evidence')
    return {str(p.relative_to(root)): sha(p)
            for p in sorted(root.rglob('*')) if p.is_file()}


def checked_manifest(root):
    files = inventory(root)
    require({k: v for k, v in files.items() if k != 'manifest.json'}
            == read(root / 'manifest.json'), 'Recording manifest differs: ' + str(root))


def archive(label, source):
    files = inventory(source)
    write(ROOT / (label + '-files.json'), files)
    destination = ROOT / (label + '.tar.gz')
    with destination.open('wb') as raw:
        with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0, compresslevel=9) as zipped:
            with tarfile.open(fileobj=zipped, mode='w') as output:
                for name in files:
                    data = (source / name).read_bytes()
                    item = tarfile.TarInfo(name)
                    item.size, item.mode, item.mtime = len(data), 0o644, 0
                    output.addfile(item, io.BytesIO(data))
    with tarfile.open(destination) as check:
        members = check.getmembers()
        require(len(members) == len(files) and {m.name for m in members} == set(files),
                'Archive inventory differs')
        require(all(m.isfile() and hashlib.sha256(check.extractfile(m).read()).hexdigest()
                    == files[m.name] for m in members), 'Archive member differs')
    return {'files': len(files), 'uncompressed_bytes': sum((source / n).stat().st_size for n in files),
            'archive_sha256': sha(destination),
            'inventory_sha256': sha(ROOT / (label + '-files.json'))}


def main():
    require(not ROOT.exists() and not any((p / '.git').exists() for p in (ROOT, *ROOT.parents)),
            'Fresh outside-Git output required')
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO).decode().strip()
            == PRODUCER, 'Exact producer commit required')
    require(not subprocess.check_output(['git', 'status', '--porcelain'], cwd=REPO).strip(),
            'Clean producer checkout required')
    export = SOURCES['export']
    for source in (export, SOURCES['replay'], SOURCES['controls'],
                   SOURCES['controls'] / 'positive-source-only-replay',
                   SOURCES['installed-wheel'] / 'source-only-replay'):
        checked_manifest(source)
    positive_roots = [export, SOURCES['replay'],
                      SOURCES['controls'] / 'positive-source-only-replay',
                      SOURCES['installed-wheel'] / 'source-only-replay']
    reports = [read(p / 'results.json') for p in positive_roots]
    original = reports[0]
    for root, report in zip(positive_roots, reports):
        require(report['status'] == 'verified-source-bound-full-PTX-GEMM'
                and report['source_bound_proof_accepted'] is True
                and report['shapes'] == [[64, 256], [256, 512], [64, 512]]
                and report['dtypes'] == ['float16', 'float16', 'float16'] and report['PTX_instructions'] == 171
                and report['launch'] == {'grid': 32768, 'block': 1, 'warp': 32}
                and report['unchanged_CUDA_contract_fuel'] == [1030, 1, 1, 1]
                and report['main_sha256'] == original['main_sha256'] == sha(root / 'Main.lean')
                and report['input_bindings'] == original['input_bindings']
                and type(report['owned_Lean_modules_freshly_compiled']) is int
                and report['owned_Lean_modules_freshly_compiled'] == 5
                and report['old_owned_olean_cache_used'] is False
                and len(report['axiom_audits']) == 6
                and len(report['library_axiom_audits']) == 169
                and all(set(v) <= ALLOWED for v in [*report['axiom_audits'].values(),
                                                    *report['library_axiom_audits'].values()])
                and all(c['exit_code'] == 0 and c['timed_out'] is False
                        for c in [*report['module_checks'], report['main_check']]),
                'Completed matching fresh proof and standard-axiom checks required')
        for name, digest in report['input_bindings'].items():
            require(sha(root / name) == digest, 'Input binding differs')
        require(report['limits'] == {'maxRecDepth': 10000, 'maxHeartbeats': 2000000,
                                    'per_Lean_process_seconds': 180,
                                    'source_import_build_seconds': 600}, 'Proof budget differs')
        for name, digest in read(root / 'source-bindings.json').items():
            current = REPO / ('lark_kernels/' + name[7:] if name.startswith('python/') else name)
            require(sha(current) == digest, 'Trusted current source differs')
    require(original['input_bindings'] == {'kernel.ptx': '896f2337328f9bb0b62975117174405f0eab90560fe91c672beb31094e86c74c',
            'reference.py': '18cc07d00af098bcc9c2d94fb5b3805f4264c810d64ca9814c07e9e25f0db466',
            'contract.json': '2a2eb23fa4daf7b7a97bb7024e2e53648952698b0f6747e5609e89f3b4309f41'},
            'Exact full-size compiler-study inputs required')
    controls = read(SOURCES['controls'] / 'results.json')
    require(controls['status'] == 'full-size-PTX-GEMM-source-controls-passed'
            and controls['positive_controls'] == 1 and controls['direct_Lean_negative_controls'] == 4
            and controls['timeouts'] == 0
            and all(c['reader_accepted'] is True and c['Lean']['exit_code'] != 0
                    and c['Lean']['timed_out'] is False
                    and c['channel'] == 'source-program-equality-proof-refused'
                    for c in controls['negative_controls']), 'Four direct Lean controls required')
    installed = read(SOURCES['installed-wheel'] / 'results.json')
    wheel = SOURCES['wheel-build'] / 'lark_kernels-0.2.0-py3-none-any.whl'
    require(installed['status'] == 'installed-wheel-source-only-PTX-GEMM-replay-passed'
            and installed['exit_code'] == 0 and installed['checkout_imported'] is False
            and installed['isolated_mode'] is True
            and installed['network_during_install_and_replay'] is False
            and installed['git_on_PATH'] is False and installed['all_owned_source_bindings_match'] is True
            and installed['legacy_ReLU_owned_source_bindings_match'] is True
            and installed['legacy_ReLU_Main_regenerated_identically'] is True
            and all(installed[k] is True for k in ('legacy_GEMV_52_source_bindings_unchanged',
                'legacy_GEMV_Main_regenerated_identically', 'legacy_GEMV_new_source_roster_refused_before_output',
                'legacy_GEMV_frozen_0_1_wheel_hash_unchanged'))
            and installed['wheel_sha256'] == sha(wheel), 'Isolated installed-wheel replay required')
    ROOT.mkdir()
    archives = {label: archive(label, source) for label, source in SOURCES.items()}
    for source, name in [(export / 'results.json', 'proof-results.json'),
                         (SOURCES['replay'] / 'replay.json', 'replay-results.json'),
                         (SOURCES['controls'] / 'results.json', 'controls-results.json'),
                         (SOURCES['installed-wheel'] / 'results.json', 'installed-wheel-results.json'),
                         (SOURCES['wheel-build'] / 'build-results.json', 'wheel-build-results.json')]:
        shutil.copyfile(source, ROOT / name)
    result = {
        'schema': 1, 'status': 'exact-source-full-size-PTX-GEMM-proof-evidence',
        'packaged_at_utc': datetime.now(timezone.utc).isoformat(),
        'producer_commit': PRODUCER, 'profile': original['profile'],
        'independent_source_bound_development_proofs': 1,
        'retained_positive_Main_checks': 4, 'positive_rechecks': 3,
        'owned_module_builds_across_four_checks': 20,
        'direct_Lean_negative_controls': 4, 'negative_timeouts': 0,
        'shapes': [[64, 256], [256, 512], [64, 512]], 'dtype': 'float16', 'PTX_instructions': 171,
        'library_axiom_audits_per_check': 169, 'Main_axiom_audits_per_check': 6,
        'launch': original['launch'], 'unchanged_CUDA_contract_fuel': [1030, 1, 1, 1],
        'input_bindings': original['input_bindings'], 'main_sha256': original['main_sha256'],
        'lean_binary_sha256': original['lean_binary_sha256'], 'limits': original['limits'],
        'wheel_sha256': sha(wheel), 'archives': archives,
        'new_registered_source_certificates': 0,
        'packaging_driver_sha256': sha(Path(__file__)),
        'packaging_model_calls': 0, 'packaging_Lean_checks': 0, 'packaging_gpu_trials': 0,
        'model_calls_for_this_proof_study': 0, 'gpu_trials_for_this_proof_study': 0,
        'nvidia_execution': False, 'original_paper_fully_reproduced': False,
        'scope': original['scope'],
    }
    write(ROOT / 'results.json', result)
    shutil.copyfile(Path(__file__), ROOT / 'packaging-driver.py')
    (ROOT / 'RESULTS.md').write_text("# Exact-source full-size FP16 PTX GEMM proof\n\nOne independent 64×256 by 256×512 FP16 matrix-multiply program has a\nsource-bound Lean proof through a separate development checker. The exact\nNVRTC 12.9.86 PTX 8.8/sm_80 source contains 171 instructions. All original\nshapes and dtypes, grid 32768/block one/warp 32 and CUDA fuel [1030,1,1,1]\nremain unchanged.\n\nThe complete parsed program and independently closed Python reference AST are\nbound in the immutable Main. Lean checks the 47-instruction prologue, all sixteen\niterations of the real backward loop, pointer/counter/predicate control, output\nstore and ret. The complete-launch theorem covers all 32,768 active lanes, race\nfreedom of actual memory events, every extracted output against the ordered\n256-term interpretation of `(a.float() @ b.float()).half()`, and preservation\noutside the output footprint. Successful instruction transitions establish\nexecution without a new fuel or an assumed loop summary. CUDA fuel remains\nseparate model data.\n\nFour retained positive Main checks passed: SDK export, dedicated outside-checkout\nreplay with Git absent from PATH, the controls' fresh positive replay, and an\nisolated installed-wheel replay. Each compiles all five owned Lean modules from\nmatched trusted source: 20 fresh module builds, 169 library axiom audits and\nsix Main audits per check. Only propext, Classical.choice and Quot.sound occur.\nNo old owned olean cache is loaded. These are repeated checks of ONE kernel.\n\nFour accepted-grammar changes fail directly in Lean at source_program: wrong\nproduct, loop-counter stride, B pointer stride and conflicting output address.\nNone times out. All task/launch/fuel data remains unchanged. These are fixed\nsource-binding controls, not a general incorrect-kernel classifier or the\npaper's original 42 mutants.\n\nThe 0.2.0 wheel was built offline with setuptools 80.9.0 and wheel 0.45.1,\ninstalled without dependencies and replayed with isolated Python outside Git.\nAll 55 source bindings and the Main match. The prior ReLU profile's source pins\nand Main remain identical. All 52 frozen GEMV source bindings and its Main also\nremain unchanged, but its 0.1 recording correctly refuses the two additional SDK\nmodules before creating output. That frozen recording requires its recorded\n0.1 wheel; no source pin was relaxed. A first installed-wheel probe expected the\nlater source-binding refusal rather than the earlier exact-roster refusal; its\nfailure is retained separately and is not counted as a replay.\n\nPython parsing/reference formalization, logical pointer provenance, aligned\ndisjoint non-wrapping host allocations and scalar-operation correspondence remain\ntrusted. The proof uses declared abstract scalar semantics. It establishes no\nIEEE rounding/error bound, PyTorch backend equivalence, NVIDIA execution or\nconformance, original optimized kernel, original model result or paper table.\nNo legacy SDK profile is registered, and no model call or GPU trial was made.\nThe six fixed-scaffold model cohorts remain unchanged. Broader full-size PTX\nfamilies and the original artifacts/experiments remain unfinished or unavailable.\n\nFive deterministic archives preserve the actual export, replay, controls,\ninstalled-wheel validation and wheel build, with complete member inventories and\nround-trip checks. Captured Python/Lean/oleans are data. Replay uses matched\ncurrent trusted source and a fresh import root. Limits remain maxRecDepth 10000,\nmaxHeartbeats 2000000, 180 seconds per Lean process and 600 seconds per import\naggregate; legacy libraries retain their source limits.\nSee [the development checker commands](../../MATRIX.md).\n")
    failed = Path('/tmp/lark-ptx-matrix-wheel-validation-v1-20261113')
    write(ROOT / 'initial-installed-wheel-probe-failure.json', {
        'status': 'failed-before-any-GEMM-replay', 'exit_code': 1,
        'probe_stderr': (failed / 'probe.stderr').read_text(),
        'probe_stderr_sha256': sha(failed / 'probe.stderr'),
        'explanation': 'Driver expected later source-binding refusal; actual earliest exact-roster refusal was correct. Only driver expectation fixed in fresh v2. SDK/wheel/limits unchanged; failed v1 never counted.'})

    shutil.copyfile('/tmp/lark-ptx-matrix-replay-cwd-v1-20261113/transport.json',
                    ROOT / 'dedicated-replay-environment.json')
    write(ROOT / 'local-test-terminal-observations.json', {
        'schema': 1, 'kind': 'terminal-observations-not-a-new-test-run',
        'source_commit': PRODUCER,
        'matrix_and_frontend': {'tool_session': 21368, 'exit_code': 0,
            'tests': 15, 'seconds': 112.028, 'status': 'OK'},
        'existing_GEMV_and_ReLU': {'tool_session': 99652, 'exit_code': 0,
            'tests': 14, 'seconds': 77.330, 'status': 'OK'},
        'source_and_Lean_bindings_match_export': True,
        'model_calls': 0, 'gpu_trials': 0,
        'note': 'Actual tests were observed at terminal. This receipt summarizes those observations; no rerun was made to manufacture captured logs.'})
    write(ROOT / 'manifest.json', inventory(ROOT))
    print(json.dumps({'output': str(ROOT), 'files': len(list(ROOT.iterdir())),
                      'bytes': sum(p.stat().st_size for p in ROOT.iterdir()),
                      'manifest_sha256': sha(ROOT / 'manifest.json')}))


if __name__ == '__main__':
    main()
