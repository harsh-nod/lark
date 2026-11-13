"""Package actual BMM proof recordings and selected development history; run no proof."""

from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
import math
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

REPO = Path('/tmp/lark-ptx-batched-refinement-20261113')
ROOT = Path('/tmp/lark-ptx-batched-proof-packet-v1-20261113')
SDK_PRODUCER = '8f381dbe0dc8a0213237566ca3520baa73ff6034'
INITIAL_PRODUCER = '65928f01c164802ee11322f5cd863b6356778641'
PACKAGING_HEAD = '130bc4d571f45409f485b9017a0cb2e5f08e32eb'
SOURCES = {
    'export': Path('/tmp/lark-ptx-batched-source-export-v3-20261113'),
    'replay': Path('/tmp/lark-ptx-batched-source-replay-v1-20261113'),
    'controls': Path('/tmp/lark-ptx-batched-source-controls-v1-20261113'),
    'installed-wheel': Path('/tmp/lark-ptx-batched-wheel-validation-v1-20261113'),
    'wheel-build': Path('/tmp/lark-ptx-batched-wheel-v1-20261113'),
    'initial-export-v1': Path('/tmp/lark-ptx-batched-source-export-v1-20261113'),
    'failed-export-v2': Path('/tmp/lark-ptx-batched-source-export-v2-20261113'),
    'sdk-tests': Path('/tmp/lark-ptx-batched-sdk-tests-v1-20261113'),
}
DEVELOPMENT = {
    'library-kernel-v1': Path('/tmp/lark-ptx-batched-kernel-correct-v1-20261113'),
    'library-kernel-v2': Path('/tmp/lark-ptx-batched-kernel-correct-v2-20261113'),
    'cached-main-spec-v1': Path('/tmp/lark-ptx-batched-main-spec-eq-v1-20261113'),
    'cached-main-spec-v2-failed': Path('/tmp/lark-ptx-batched-main-spec-eq-v2-20261113'),
    'cached-main-profile-v1': Path('/tmp/lark-ptx-batched-main-profile-v1-20261113'),
    'cached-main-direct-reference-v1': Path('/tmp/lark-ptx-batched-main-reference-direct-v1-20261113'),
}
INPUTS = {
    'kernel.ptx': 'df13d4a76ce01ff72fb71eeeca866c5750885bb29d036c652ec9036c7c97cd81',
    'reference.py': '18cc07d00af098bcc9c2d94fb5b3805f4264c810d64ca9814c07e9e25f0db466',
    'contract.json': 'babf31898308958c10e664b63bfb2b03ad13bb1736e259fd857d40640d98fadc',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
sys.path.insert(0, str(REPO))
from lark_kernels import ptx_batched as reader  # noqa: E402
from lark_kernels import ptx_batched_certificate as checker  # noqa: E402


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
    require(not any(p.is_symlink() for p in root.rglob('*')), 'Evidence symlink')
    return {p.relative_to(root).as_posix(): sha(p) for p in sorted(root.rglob('*')) if p.is_file()}


def checked_manifest(root):
    actual = inventory(root)
    require({k: v for k, v in actual.items() if k != 'manifest.json'} == read(root / 'manifest.json'),
            'Exact recording inventory differs: ' + str(root))


def archive(label, source):
    files = inventory(source)
    write(ROOT / (label + '-files.json'), files)
    target = ROOT / (label + '.tar.gz')
    with target.open('wb') as raw:
        with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0, compresslevel=9) as zipped:
            with tarfile.open(fileobj=zipped, mode='w') as output:
                for name in files:
                    data = (source / name).read_bytes()
                    item = tarfile.TarInfo(name)
                    item.size, item.mode, item.mtime = len(data), 0o644, 0
                    output.addfile(item, io.BytesIO(data))
    with tarfile.open(target) as check:
        members = check.getmembers()
        require(len(members) == len(files) and {m.name for m in members} == set(files), 'Archive roster')
        require(all(m.isfile() and hashlib.sha256(check.extractfile(m).read()).hexdigest() == files[m.name]
                    for m in members), 'Archive member bytes')
    return {'files': len(files), 'uncompressed_bytes': sum((source / n).stat().st_size for n in files),
            'archive_bytes': target.stat().st_size, 'archive_sha256': sha(target),
            'inventory_sha256': sha(ROOT / (label + '-files.json'))}


def git_source(commit, name):
    path = 'lark_kernels/' + name[7:] if name.startswith('python/') else name
    return subprocess.check_output(['git', 'show', commit + ':' + path], cwd=REPO)


def verify_export(root, producer, expected_main=None):
    checked_manifest(root)
    r = read(root / 'results.json')
    sources = {n: (root / 'owned-sources' / n).read_bytes()
               for n in read(root / 'source-bindings.json')}
    require(len(sources) == 60 and sum(n.startswith('python/') for n in sources) == 52, 'Full60 sources')
    bindings = {n: hashlib.sha256(v).hexdigest() for n, v in sources.items()}
    require(bindings == read(root / 'source-bindings.json'), 'Owned source bytes')
    for name, content in sources.items():
        require(git_source(producer, name) == content, 'Producer Git source differs: ' + name)
    require(r['status'] == 'verified-source-bound-full-PTX-BMM'
            and r['profile'] == reader.PROFILE and r['scope'] == checker.SCOPE
            and r['source_bound_proof_accepted'] is True and r['source_bound_development_proofs'] == 1
            and type(r['source_bound_development_proofs']) is int
            and r['input_bindings'] == INPUTS and all(sha(root / n) == h for n, h in INPUTS.items())
            and checker.same_json(r['shapes'], [[32, 64, 256], [32, 256, 512], [32, 64, 512]])
            and r['dtypes'] == ['float16'] * 3 and type(r['PTX_instructions']) is int
            and r['PTX_instructions'] == 138
            and checker.same_json(r['launch'], {'grid': 1048576, 'block': 1, 'warp': 32})
            and checker.same_json(r['unchanged_CUDA_contract_fuel'], [1030, 1, 1, 1])
            and checker.same_json(r['limits'], checker.LIMITS)
            and r['lean_binary_sha256'] == checker.LEAN_SHA256
            and type(r['owned_Lean_modules_freshly_compiled']) is int
            and r['owned_Lean_modules_freshly_compiled'] == 8
            and r['old_owned_olean_cache_used'] is False
            and r['original_paper_fully_reproduced'] is r['nvidia_execution'] is False
            and all(type(r[k]) is int and r[k] == 0 for k in
                    ('model_calls', 'gpu_trials', 'new_registered_source_certificates')),
            'Completed unchanged full-size source-bound proof scope')
    require(r['source_bindings_sha256'] == sha(root / 'source-bindings.json')
            and r['main_sha256'] == sha(root / 'Main.lean')
            and (expected_main is None or r['main_sha256'] == expected_main), 'Proof source identities')
    expected_paths = checker.expected_paths(sources)
    if (root / 'replay.json').exists():
        expected_paths |= {'replay.json', 'proof-export-manifest.json'}
    require(set(read(root / 'manifest.json')) == expected_paths, 'Exact positive export roster')
    tags = ['LarkPtxBatchedCertificate.' + n for n in reader.TAGS]
    require(r['axiom_audits'] == checker.common.audits((root / 'Main.log').read_text(), tags)
            and len(r['axiom_audits']) == 6
            and checker.valid_check(r['main_check'], (root / 'Main.log').read_bytes(), ['Main.lean']),
            'Actual accepted Main/axiom check')
    require([row['module'] for row in r['module_checks']] == ['Lark.' + n for n in checker.MODULES],
            'All8 actual module checks')
    library = {}
    for name, row in zip(checker.MODULES, r['module_checks'], strict=True):
        require(checker.valid_check(row, (root / (name + '.log')).read_bytes(),
                    ['-o', 'Lark/' + name + '.olean', 'Lark/' + name + '.lean'])
                and (root / 'modules/Lark' / (name + '.lean')).read_bytes() == sources['lean/Lark/' + name + '.lean'],
                'Actual module source/log/budget check')
        library.update(checker.common.audits((root / (name + '.log')).read_text(), checker.library_tags(sources, name)))
    require(r['library_axiom_audits'] == library and len(library) == 271
            and all(set(v) <= ALLOWED for v in [*library.values(), *r['axiom_audits'].values()]),
            'All271 actual standard library axiom audits')
    elapsed = r['import_build_seconds']
    require(type(elapsed) in (int, float) and math.isfinite(elapsed) and 0 <= elapsed <= 600, 'Import cap')
    return r


def main():
    require(not ROOT.exists() and not any((p / '.git').exists() for p in (ROOT, *ROOT.parents)), 'Fresh no-Git packet')
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip() == PACKAGING_HEAD
            and not subprocess.check_output(['git', 'status', '--porcelain'], cwd=REPO, text=True).strip(),
            'Clean pinned packaging checkout')
    roots = [SOURCES['export'], SOURCES['replay'], SOURCES['controls'] / 'positive-source-only-replay',
             SOURCES['installed-wheel'] / 'source-only-replay']
    original = verify_export(roots[0], SDK_PRODUCER)
    reports = [original, *[verify_export(p, SDK_PRODUCER, original['main_sha256']) for p in roots[1:]]]
    current_sources = checker.own_sources()
    require(read(roots[0] / 'source-bindings.json') == {n: checker.sha(v) for n, v in current_sources.items()},
            'All60 current trusted source bytes')
    for p in (SOURCES['controls'], SOURCES['installed-wheel'], SOURCES['wheel-build'], SOURCES['sdk-tests']):
        checked_manifest(p)
    controls = read(SOURCES['controls'] / 'results.json')
    require(controls['status'] == 'full-size-PTX-BMM-source-controls-passed'
            and controls['positive_controls'] == 1 and controls['direct_Lean_negative_controls'] == 4
            and controls['timeouts'] == 0 and controls['owned_modules_freshly_compiled'] == 8
            and controls['old_owned_olean_cache_used'] is False
            and {c['control'] for c in controls['negative_controls']} ==
              {'wrong-product', 'wrong-loop-counter-stride', 'wrong-B-pointer-stride', 'shifted-output-address'},
            'All4 actual dedicated controls')
    for row in controls['negative_controls']:
        folder = SOURCES['controls'] / row['control']
        text, log = (folder / 'Main.lean').read_text(), (folder / 'Main.log').read_text()
        line = next(i+1 for i, value in enumerate(text.splitlines()) if value.startswith('theorem source_program '))
        require(row['reader_accepted'] is True and row['source_fragments_changed'] == 1
                and row['PTX_instructions'] == 138 and row['all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged'] is True
                and type(row['Lean']['exit_code']) is int and row['Lean']['exit_code'] != 0
                and row['Lean']['timed_out'] is False and f'Main.lean:{line}:' in log
                and "tactic 'decide' proved that" in log and 'is false' in log
                and not any(s in log for s in ('maximum recursion', 'maximum number of heartbeats', 'Stack overflow'))
                and row['Lean']['log_sha256'] == sha(folder / 'Main.log')
                and row['channel'] == 'source-program-equality-proof-refused'
                and row['general_kernel_falsity_claim'] is False, 'Actual bounded source-program refusal')
    installed = read(SOURCES['installed-wheel'] / 'results.json')
    wheel = SOURCES['wheel-build'] / 'lark_kernels-0.3.0-py3-none-any.whl'
    require(installed['status'] == 'installed-wheel-source-only-PTX-BMM-replay-passed'
            and installed['exit_code'] == 0 and installed['checkout_imported'] is False
            and installed['isolated_mode'] is True and installed['git_on_PATH'] is False
            and installed['network_during_install_and_replay'] is False
            and installed['all60_owned_source_bindings_match'] is True
            and all(installed[k] is True for k in ('legacy_ReLU_source_and_Main_unchanged',
                'legacy_GEMV52_source_bytes_and_Main_unchanged', 'legacy_GEMM55_source_bytes_and_Main_unchanged',
                'legacy_GEMV_and_GEMM_enlarged_rosters_refused_before_output',
                'initial_BMM_renderer_source_change_refused_before_output', 'frozen_0_1_and_0_2_wheel_hashes_unchanged'))
            and installed['wheel_sha256'] == sha(wheel) == '456d0e3f8f2a24c1cb978d0ee6f5455d918387a417f03c39256299106ea10173',
            'Isolated installed matching-wheel replay and strict legacy compatibility')
    initial = verify_export(SOURCES['initial-export-v1'], INITIAL_PRODUCER)
    old_bindings = read(SOURCES['initial-export-v1'] / 'source-bindings.json')
    current_bindings = read(roots[0] / 'source-bindings.json')
    require(set(old_bindings) == set(current_bindings)
            and {n for n in current_bindings if old_bindings[n] != current_bindings[n]} == {'python/ptx_batched.py'},
            'Exactly the historical renderer differs')
    failed = SOURCES['failed-export-v2']
    checked_manifest(failed)
    failure = read(failed / 'results.json')
    require(failure['status'] == 'unproved-source-bound-PTX-BMM'
            and failure['source_bound_proof_accepted'] is False and failure['source_bound_development_proofs'] == 0
            and failure['owned_Lean_modules_freshly_compiled'] == 8
            and failure['main_check']['exit_code'] == 1 and failure['main_check']['timed_out'] is False
            and 'maximum recursion depth' in (failed / 'Main.log').read_text()
            and failure['limits'] == checker.LIMITS, 'Retained real failed v2, no cap change')
    tests = read(SOURCES['sdk-tests'] / 'results.json')
    require(tests['status'] == 'BMM-SDK-complete-proof-replay-adversarial-test-passed'
            and tests['exit_code'] == 0 and tests['timed_out'] is False
            and tests['test_source_sha256'] == sha(REPO / 'tests/test_ptx_batched.py'), 'Actual SDK integration test')
    ROOT.mkdir()
    archives = {label: archive(label, source) for label, source in SOURCES.items()}
    selected = ROOT / 'development-work'
    selected.mkdir()
    for label, source in DEVELOPMENT.items():
        shutil.copytree(source, selected / label)
    archives['development-history'] = archive('development-history', selected)
    shutil.rmtree(selected)
    copies = [(roots[0] / 'results.json', 'proof-results.json'),
              (SOURCES['replay'] / 'replay.json', 'replay-results.json'),
              (SOURCES['controls'] / 'results.json', 'controls-results.json'),
              (SOURCES['installed-wheel'] / 'results.json', 'installed-wheel-results.json'),
              (SOURCES['wheel-build'] / 'build-results.json', 'wheel-build-results.json'),
              (SOURCES['initial-export-v1'] / 'results.json', 'initial-export-results.json'),
              (failed / 'results.json', 'failed-export-results.json'),
              (SOURCES['sdk-tests'] / 'results.json', 'sdk-test-results.json'),
              (REPO / 'tests/test_ptx_batched.py', 'sdk-test-source.py')]
    for source, name in copies:
        shutil.copyfile(source, ROOT / name)
    history = {'schema': 1, 'initial_success': {'producer': INITIAL_PRODUCER, 'Main_sha256': initial['main_sha256'],
               'Main_seconds': initial['main_check']['seconds'], 'fresh_owned_modules': 8},
               'failed_v2': {'Main_seconds': failure['main_check']['seconds'], 'accepted': False,
               'cause': 'spec_eq rfl normalized optional million-element reference and reached existing maxRecDepth 10000'},
               'final_current_source': {'producer': SDK_PRODUCER, 'main_sha256': original['main_sha256'],
               'source_bindings_sha256': original['source_bindings_sha256'], 'current_pipeline_checks': 4,
               'same_independent_kernel': True},
               'selected_development_history': list(DEVELOPMENT),
               'cached_development_positive_Main_checks': 3, 'cached_development_failed_Main_checks': 1,
               'cached_development_fresh_owned_imports': 0,
               'pure_library_development_checks': 2,
               'cached_development_counts_as_source_only_export': False,
               'explanation': 'Both SDK revisions prove the same concrete full-size program. The initial successful '
               'SDK used an optional reference wrapper and took 91.77 seconds. A genuine intermediate export failed at '
               'maxRecDepth 10000. Profiling found type checking expanded the optional reference list; the final '
               'SDK checks AST denotation directly and retains every proof obligation. No cap/shape/fuel changed. '
               'Selected cached development Main checks and library checks are retained separately, including '
               'the failed unavailable congrArg₂ prototype; none is counted as a fresh source-only export.'}
    write(ROOT / 'validation-history.json', history)
    result = {'schema': 1, 'status': 'exact-source-full-size-PTX-BMM-proof-evidence',
              'packaged_at_utc': datetime.now(timezone.utc).isoformat(), 'producer_commit': SDK_PRODUCER,
              'packaging_source_commit': PACKAGING_HEAD, 'profile': original['profile'],
              'independent_source_bound_development_proofs': 1,
              'retained_positive_Main_checks': 5, 'positive_rechecks': 4,
              'current_SDK_positive_Main_checks': 4, 'initial_SDK_positive_Main_checks': 1,
              'owned_module_builds_across_four_current_checks': 32,
              'owned_module_builds_across_five_successful_official_checks': 40,
              'retained_failed_official_exports': 1, 'failed_export_fresh_owned_modules': 8,
              'cached_development_positive_Main_checks': 3,
              'cached_development_counts_as_official_positive_Main_checks': False,
              'unit_test_positive_Main_recordings_retained': 0,
              'direct_Lean_negative_controls': 4, 'negative_timeouts': 0,
              'shapes': original['shapes'], 'dtype': 'float16', 'PTX_instructions': 138,
              'library_axiom_audits_per_check': 271, 'Main_axiom_audits_per_check': 6,
              'launch': original['launch'], 'unchanged_CUDA_contract_fuel': [1030, 1, 1, 1],
              'input_bindings': INPUTS, 'main_sha256': original['main_sha256'],
              'source_bindings_sha256': original['source_bindings_sha256'], 'owned_source_files': 60,
              'lean_binary_sha256': original['lean_binary_sha256'], 'limits': original['limits'],
              'wheel_sha256': sha(wheel), 'archives': archives, 'new_registered_source_certificates': 0,
              'packaging_driver_sha256': sha(Path(__file__)), 'packaging_model_calls': 0,
              'packaging_Lean_checks': 0, 'packaging_gpu_trials': 0,
              'model_calls_for_this_proof_study': 0, 'gpu_trials_for_this_proof_study': 0,
              'nvidia_execution': False, 'original_paper_fully_reproduced': False, 'scope': original['scope']}
    write(ROOT / 'results.json', result)
    shutil.copyfile(Path(__file__), ROOT / 'packaging-driver.py')
    (ROOT / 'RESULTS.md').write_text('''# Exact-source full-size FP16 PTX batched GEMM proof

One independent compiled BMM program now has a source-bound Lean proof for
A[32,64,256] times B[32,256,512], producing out[32,64,512], all FP16. The original
grid 1048576/block 1/warp 32 and CUDA fuel [1030,1,1,1] remain unchanged. The NVRTC
12.9.86 PTX 8.8/sm_80 program retains all 138 instructions and 149 declared registers.

Lean checks the 29-instruction prologue, actual 98-instruction body, five control
instructions and six-instruction epilogue. All sixteen actual loop iterations
compose from real source transitions through ret. The same whole-launch witness
covers all 1,048,576 lanes, race freedom over the actual recorded memory events,
every extracted output against the closed ordered 256-term reference AST, and
preservation of memory outside the output footprint. No loop summary is assumed.
The original CUDA fuel remains separate model data; PTX execution is an inductive
sequence of successful transitions and introduces no new execution fuel.

Four current-SDK positive Main checks passed: source export, fresh replay outside
Git with Git absent from PATH, the controls' fresh positive replay, and isolated
installed-wheel replay. Each builds all eight owned libraries from matched
trusted source: 32 fresh module builds, 271 library axiom audits and six Main audits
per check. Only propext, Classical.choice and Quot.sound occur. No old owned
compiled object is loaded. The final Main checks in about 1.7 seconds locally.

A genuine earlier SDK export also passed with eight fresh libraries and a
91.77-second Main check. It is preserved with its different renderer source pins.
The five retained official positive Main recordings are repeated checks of ONE
kernel: 40 successful fresh module builds and four positive rechecks. An actual
intermediate export failed at the unchanged maxRecDepth 10000 and is retained as
a failure. Selected cached development checks, including an unavailable-helper
failure and profiling, are separate history and count as no source-only export.
The SDK unit test passed fresh export/replay, one direct source refusal and ten
coherently rehashed tampering refusals. Its temporary Main files are not retained
positive recordings or extra independent kernels.

Four accepted-grammar mutations fail directly at source_program by decide:
product, loop-counter stride, B-pointer stride and shifted output address.
All four retain the shapes, launch, dtypes and fuel. None times out. These are
fixed-profile source-binding controls, not a general false-kernel classifier or
the original paper's 42 mutants.

The 0.3.0 wheel was built offline with setuptools 80.9.0 and wheel 0.45.1. Isolated
Python installed it without dependencies and replayed outside the checkout with
Git absent. All 60 owned source bytes match. Earlier ReLU source/Main bytes remain
identical. All 52 GEMV and 55 GEMM frozen source bindings and their Main bytes also
remain unchanged; their enlarged current rosters correctly refuse old recordings
before creating output. Their frozen 0.1/0.2 wheel hashes are unchanged. The initial
BMM renderer recording likewise requires its own exact source identity; no pin
is relaxed to accept the later renderer.

Python parsing/reference formalization, logical pointer provenance, aligned
disjoint non-wrapping allocations and scalar-operation correspondence remain
trusted. The proof uses declared abstract scalar semantics. It establishes no
IEEE rounding/error bound, PyTorch backend equivalence, NVIDIA execution or
conformance, original optimized program, original model result or paper table.
No legacy SDK profile is registered. No model call or GPU trial was made.

Deterministic archives retain the complete official recordings, wheel build,
actual failed export, SDK test logs and selected development history. Every
member has a SHA256 inventory and a round-trip byte check. Captured Python,
Lean and compiled objects are data. Replay uses matched current trusted source
and fresh imports. Limits remain 180 seconds per Lean process, 600 seconds per
import aggregate, maxRecDepth 10000 and maxHeartbeats 2000000; legacy library
source limits are preserved. See [the checker commands](../../BATCHED.md).
''')
    write(ROOT / 'dedicated-replay-environment.json', {
        'kind': 'recorded-tool-invocation-observation-not-a-new-replay', 'tool_session': 43469,
        'terminal_exit_code': 0, 'cwd': '/tmp', 'PATH': '/nonexistent',
        'PYTHONPATH': str(REPO), 'trusted_SDK_loaded_from_current_source': True,
        'captured_Python_executed': False, 'git_on_PATH': False,
        'installed_wheel_replay_separately_records_its_isolated_environment': True})
    write(ROOT / 'local-test-terminal-observations.json', {
        'kind': 'terminal-observations-not-new-tests', 'reader_regression_session': 55431,
        'reader_regression_tests': 26, 'reader_regression_seconds': 1.000, 'reader_regression_exit': 0,
        'SDK_integration_session': 17773, 'SDK_integration_exit': 0,
        'SDK_integration_seconds': tests['seconds'], 'model_calls': 0, 'gpu_trials': 0})
    write(ROOT / 'manifest.json', inventory(ROOT))
    print(json.dumps({'status': result['status'], 'output': str(ROOT), 'archives': len(archives),
          'files': len(list(ROOT.iterdir())), 'bytes': sum(p.stat().st_size for p in ROOT.iterdir()),
          'manifest_sha256': sha(ROOT / 'manifest.json')}), flush=True)


if __name__ == '__main__':
    main()
