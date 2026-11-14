"""Package actual Linear proof recordings and every retained development attempt; run no proof."""
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
import zipfile

REPO = Path('/tmp/lark-ptx-linear-refinement-20261113')
ROOT = Path('/tmp/lark-ptx-linear-proof-packet-v1-20261113')
SDK_PRODUCER = 'fb405c06d6dfd96ca8af965dae0da6888d56b8c6'
PACKAGING_HEAD = '8efb14df662ec0d69187ddc8d1bb8e01b5fca49a'
SOURCES = {
    'export': Path('/tmp/lark-ptx-linear-source-export-v1-20261113'),
    'replay': Path('/tmp/lark-ptx-linear-source-replay-v1-20261113'),
    'controls': Path('/tmp/lark-ptx-linear-source-controls-v1-20261113'),
    'installed-wheel': Path('/tmp/lark-ptx-linear-wheel-validation-v1-20261113'),
    'wheel-build': Path('/tmp/lark-ptx-linear-wheel-v1-20261113'),
    'sdk-tests': Path('/tmp/lark-ptx-linear-sdk-tests-v1-20261113'),
}
DEVELOPMENT = {name: Path('/tmp/lark-ptx-linear-'+name+'-20261113') for name in (
    'prefix15-v1', 'prefix15-v2', 'address43-v1', 'address43-v2',
    'initialization-v1', 'initialization-v2', 'initialization-v3',
    'initialization-cold-v1', 'initialization-cold-v2', 'loop-v1', 'exit-v1', 'launch-v1')}
INPUTS = {
    'kernel.ptx': '5ae52a2a03b700ffebe4de2d10c69e9fc3f34dea2d99e1bd3ad1c2472ef6e273',
    'reference.py': 'e9be42251e3c805b12dab2b8cdf23a8a8d30999c4733ced7a46d7da88c13aa68',
    'contract.json': '78eef07eb3d9a315e87f3bb8bbb6e8a253d6d90a5ada37b1e48351c31dc93dd3',
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
sys.path.insert(0, str(REPO))
from lark_kernels import ptx_linear as reader
from lark_kernels import ptx_linear_certificate as checker

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
    require(len(sources) == 64 and sum(n.startswith('python/') for n in sources) == 54, 'Full64 sources')
    bindings = {n: hashlib.sha256(v).hexdigest() for n, v in sources.items()}
    require(bindings == read(root / 'source-bindings.json'), 'Owned source bytes')
    for name, content in sources.items():
        require(git_source(producer, name) == content, 'Producer Git source differs: ' + name)
    require(r['status'] == 'verified-source-bound-full-PTX-LINEAR'
            and r['profile'] == reader.PROFILE and r['scope'] == checker.SCOPE
            and r['source_bound_proof_accepted'] is True and r['source_bound_development_proofs'] == 1
            and type(r['source_bound_development_proofs']) is int
            and r['input_bindings'] == INPUTS and all(sha(root / n) == h for n, h in INPUTS.items())
            and checker.same_json(r['shapes'], [[64, 256], [256, 512], [512], [64, 512]])
            and r['dtypes'] == ['float16'] * 4 and type(r['PTX_instructions']) is int
            and r['PTX_instructions'] == 179
            and checker.same_json(r['launch'], {'grid': 32768, 'block': 1, 'warp': 32})
            and checker.same_json(r['unchanged_CUDA_contract_fuel'], [1030, 1, 1, 1])
            and checker.same_json(r['limits'], checker.LIMITS)
            and r['lean_binary_sha256'] == checker.LEAN_SHA256
            and type(r['owned_Lean_modules_freshly_compiled']) is int
            and r['owned_Lean_modules_freshly_compiled'] == 10
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
    tags = ['LarkPtxLinearCertificate.' + n for n in reader.TAGS]
    require(r['axiom_audits'] == checker.common.audits((root / 'Main.log').read_text(), tags)
            and len(r['axiom_audits']) == 6
            and checker.valid_check(r['main_check'], (root / 'Main.log').read_bytes(), ['Main.lean']),
            'Actual accepted Main/axiom check')
    require([row['module'] for row in r['module_checks']] == ['Lark.' + n for n in checker.MODULES],
            'All10 actual module checks')
    library = {}
    for name, row in zip(checker.MODULES, r['module_checks'], strict=True):
        require(checker.valid_check(row, (root / (name + '.log')).read_bytes(),
                    ['-o', 'Lark/' + name + '.olean', 'Lark/' + name + '.lean'])
                and (root / 'modules/Lark' / (name + '.lean')).read_bytes() == sources['lean/Lark/' + name + '.lean'],
                'Actual module source/log/budget check')
        library.update(checker.common.audits((root / (name + '.log')).read_text(), checker.library_tags(sources, name)))
    require(r['library_axiom_audits'] == library and len(library) == 280
            and all(set(v) <= ALLOWED for v in [*library.values(), *r['axiom_audits'].values()]),
            'All280 actual standard library axiom audits')
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
    current = checker.own_sources()
    require(len(current) == 64 and read(roots[0] / 'source-bindings.json') ==
            {n: checker.sha(v) for n, v in current.items()}, 'All64 current trusted source bytes')
    for root in roots[1:]:
        replay = read(root / 'replay.json')
        require(replay['status'] == 'fresh-source-only-PTX-LINEAR-proof-replay-passed'
                and replay['owned_modules_freshly_compiled'] == 10
                and replay['old_owned_olean_cache_used'] is False
                and replay['main_regenerated_identically'] is True
                and replay['main_sha256'] == original['main_sha256']
                and replay['recording_manifest_sha256'] == sha(roots[0] / 'manifest.json')
                and replay['source_bound_proofs_added'] == 0, 'Actual matching fresh replay')
    for label in ('controls', 'installed-wheel', 'wheel-build', 'sdk-tests'):
        checked_manifest(SOURCES[label])
    controls = read(SOURCES['controls'] / 'results.json')
    require(controls['status'] == 'full-size-PTX-LINEAR-source-controls-passed'
            and controls['positive_controls'] == 1 and controls['direct_Lean_negative_controls'] == 4
            and controls['timeouts'] == 0 and controls['owned_modules_freshly_compiled'] == 10
            and controls['old_owned_olean_cache_used'] is False
            and {r['control'] for r in controls['negative_controls']} ==
              {'wrong-product', 'wrong-sign-extension-source', 'wrong-bias-shift', 'wrong-bias-operation'},
            'All4 actual dedicated controls')
    for row in controls['negative_controls']:
        folder = SOURCES['controls'] / row['control']
        text, log = (folder / 'Main.lean').read_text(), (folder / 'Main.log').read_text()
        line = next(i+1 for i, value in enumerate(text.splitlines()) if value.startswith('theorem source_program '))
        require(row['reader_accepted'] is True and row['source_fragments_changed'] == 1
                and row['PTX_instructions'] == 179 and row['all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged'] is True
                and type(row['Lean']['exit_code']) is int and row['Lean']['exit_code'] != 0
                and row['Lean']['timed_out'] is False and f'Main.lean:{line}:' in log
                and "tactic 'decide' proved that" in log and 'is false' in log
                and not any(s in log for s in ('maximum recursion', 'maximum number of heartbeats', 'Stack overflow'))
                and row['Lean']['log_sha256'] == sha(folder / 'Main.log')
                and row['channel'] == 'source-program-equality-proof-refused'
                and row['general_kernel_falsity_claim'] is False, 'Actual bounded source-program refusal')
    installed = read(SOURCES['installed-wheel'] / 'results.json')
    wheel = SOURCES['wheel-build'] / 'lark_kernels-0.4.0-py3-none-any.whl'
    require(installed['status'] == 'installed-wheel-source-only-PTX-LINEAR-replay-passed'
            and installed['exit_code'] == 0 and installed['checkout_imported'] is False
            and installed['isolated_mode'] is True and installed['git_on_PATH'] is False
            and installed['network_during_install_and_replay'] is False
            and installed['all64_owned_source_bindings_match'] is True
            and all(installed[k] is True for k in ('legacy_ReLU_source_and_Main_unchanged',
              'legacy_GEMV52_source_bytes_and_Main_unchanged', 'legacy_GEMM55_source_bytes_and_Main_unchanged',
              'legacy_BMM60_source_bytes_and_Main_unchanged',
              'legacy_GEMV_GEMM_and_BMM_enlarged_rosters_refused_before_output',
              'frozen_0_1_0_2_and_0_3_wheel_hashes_unchanged'))
            and installed['wheel_sha256'] == sha(wheel) ==
              '264c59f4427d3c2d3c0bf3cbd82cd040de484aba54fdb938da759c196dd78f37',
            'Isolated installed matching-wheel replay and strict legacy identities')
    with zipfile.ZipFile(wheel) as archive_file:
        for name, content in current.items():
            path = ('lark_kernels/' + name[7:] if name.startswith('python/') else
                    'lark_kernels-0.4.0.data/data/share/lark/' + name)
            require(archive_file.read(path) == content, 'All64 wheel/source bytes')
    tests = read(SOURCES['sdk-tests'] / 'results.json')
    require(tests['status'] == 'LINEAR-SDK-complete-proof-replay-adversarial-test-passed'
            and tests['exit_code'] == 0 and tests['timed_out'] is False
            and tests['test_source_sha256'] == sha(REPO / 'tests/test_ptx_linear.py'),
            'Actual SDK composite test')
    ROOT.mkdir()
    archives = {}
    for label, source in SOURCES.items():
        print(json.dumps({'stage': 'archive', 'label': label}), flush=True)
        archives[label] = archive(label, source)
    selected = ROOT / 'development-work'
    selected.mkdir()
    for label, source in DEVELOPMENT.items():
        shutil.copytree(source, selected / label)
    checkpoint = read(Path('/tmp/lark-ptx-linear-checkpoint-v1-20261113/results.json'))
    history = {'schema': 1, 'retained_development_attempts': 12,
        'pre_SDK_checkpoint': checkpoint,
        'earlier_actual_terminal_exit_codes': {r['label']: r['observed_terminal_exit_code'] for r in checkpoint['records']},
        'additional_actual_terminal_observations': [
          {'label': 'exit-v1', 'tool_session': 83876, 'observed_terminal_exit_code': 0,
           'cached_owned_modules': 8, 'fresh_owned_modules': 1, 'Main_library_theorem_scope': 'complete lane only'},
          {'label': 'launch-v1', 'tool_session': 1087, 'observed_terminal_exit_code': 0,
           'cached_owned_modules': 9, 'fresh_owned_modules': 1, 'Main_library_theorem_scope': 'complete source launch/reference/race theorem'}],
        'accepted_pre_SDK_development_checks': 7, 'failed_pre_SDK_development_checks': 5,
        'failed_Lean_drafts_never_accepted': True,
        'compiler_recovery_sorryAx_in_failed_logs_is_not_an_accepted_axiom': True,
        'partial_cold_v1_driver_failure_never_accepted': True,
        'explanation': 'Every original raw development directory is retained, including all failed drafts '
            'and the audit-name driver failure. That failed cold directory retains its original partial '
            'running label; its terminal1 was observed, bound in the checkpoint and is not a live job '
            'or accepted proof. Earlier partial prologue/loop studies and cached complete-library checks '
            'are not fresh complete SDK exports or additional independent kernels. All caps, statements, '
            'shapes and fuels were retained. The final SDK is pinned independently at '+SDK_PRODUCER+'.'}
    write(selected / 'history-observations.json', history)
    print(json.dumps({'stage': 'archive', 'label': 'development-history'}), flush=True)
    archives['development-history'] = archive('development-history', selected)
    shutil.rmtree(selected)
    copies = [(roots[0] / 'results.json', 'proof-results.json'),
              (SOURCES['replay'] / 'replay.json', 'replay-results.json'),
              (SOURCES['controls'] / 'results.json', 'controls-results.json'),
              (SOURCES['installed-wheel'] / 'results.json', 'installed-wheel-results.json'),
              (SOURCES['wheel-build'] / 'build-results.json', 'wheel-build-results.json'),
              (SOURCES['sdk-tests'] / 'results.json', 'sdk-test-results.json'),
              (REPO / 'tests/test_ptx_linear.py', 'sdk-test-source.py')]
    for source, name in copies:
        shutil.copyfile(source, ROOT / name)
    write(ROOT / 'validation-history.json', history)
    result = {'schema': 1, 'status': 'exact-source-full-size-PTX-LINEAR-proof-evidence',
        'packaged_at_utc': datetime.now(timezone.utc).isoformat(), 'producer_commit': SDK_PRODUCER,
        'packaging_source_commit': PACKAGING_HEAD, 'profile': original['profile'],
        'independent_source_bound_development_proofs': 1,
        'retained_positive_Main_checks': 4, 'positive_rechecks': 3,
        'current_SDK_positive_Main_checks': 4, 'owned_module_builds_across_four_checks': 40,
        'retained_failed_official_exports': 0, 'retained_pre_SDK_development_attempts': 12,
        'accepted_pre_SDK_development_checks': 7, 'failed_pre_SDK_development_checks': 5,
        'pre_SDK_development_counts_as_official_positive_Main_checks': False,
        'unit_test_positive_Main_recordings_retained': 0,
        'direct_Lean_negative_controls': 4, 'negative_timeouts': 0,
        'shapes': original['shapes'], 'dtype': 'float16', 'PTX_instructions': 179,
        'library_axiom_audits_per_check': 280, 'Main_axiom_audits_per_check': 6,
        'launch': original['launch'], 'unchanged_CUDA_contract_fuel': [1030, 1, 1, 1],
        'input_bindings': INPUTS, 'main_sha256': original['main_sha256'],
        'source_bindings_sha256': original['source_bindings_sha256'], 'owned_source_files': 64,
        'lean_binary_sha256': original['lean_binary_sha256'], 'limits': original['limits'],
        'wheel_sha256': sha(wheel), 'archives': archives, 'new_registered_source_certificates': 0,
        'packaging_driver_sha256': sha(Path(__file__)), 'packaging_model_calls': 0,
        'packaging_Lean_checks': 0, 'packaging_gpu_trials': 0,
        'model_calls_for_this_proof_study': 0, 'gpu_trials_for_this_proof_study': 0,
        'nvidia_execution': False, 'original_paper_fully_reproduced': False, 'scope': original['scope']}
    write(ROOT / 'results.json', result)
    shutil.copyfile(Path(__file__), ROOT / 'packaging-driver.py')
    (ROOT / 'RESULTS.md').write_text("# Exact-source full-size FP16 PTX Linear proof\n\nOne independent original compiled matrix-plus-bias program has a source-bound\nLean proof for a[64,256] times b[256,512] plus bias[512], producing out[64,512],\nall FP16. The original grid32768/block1/warp32 and CUDA fuel[1030,1,1,1] remain\nunchanged. All179 instructions and189 declared registers are retained.\n\nThe same actual source witness executes the50instruction prologue, all16 real\n113instruction matrix body iterations with five controls each, and all11 bias,\nstore and return instructions. Bias is added before the final half conversion.\nAll32768lanes, actual memory-event race freedom, closed reference AST extraction\nand preservation outside output are covered. No instruction/loop summary or new\nPTX execution fuel is assumed; original CUDA fuel remains separate model data.\n\nFour complete SDK positive Main recordings check ONE kernel: source export,\nno-Git fresh replay, the controls' fresh replay and isolated installed-wheel\nreplay. Each rebuilds ten owned source modules:40fresh builds in total, with\n280library and sixMain axiom audits per check. Only propext, Classical.choice\nand Quot.sound occur. Captured Python/Lean/compiled objects are data; trusted\nmatching source regenerates Main and builds every owned import freshly.\n\nFour accepted-grammar one-fragment mutations reach the actual source_program\nLean equality and fail without timeout: product, signed-conversion source,\nbias shift and bias operation. They preserve every shape/dtype/launch/fuel.\nThey test fixed-profile binding, not general kernel falsity or the original42\npaper mutants. The full SDK integration test additionally passed fresh10export,\nfresh10replay, direct wrong-product refusal and ten coherently rehashed attacks.\nIts temporary Main files are not retained positive recordings or new kernels.\n\nAll12 pre-SDK development attempts are retained separately, including five\nfailures and seven accepted partial or library checks. They are not official\ncomplete source-only SDK exports. Failed compiler recovery logs with sorryAx\nwere never accepted. The failed first cold driver retains its original partial\nrunning label, with actual observed terminal1 recorded in history. No proof\nstatement, shape, fuel or resource cap was weakened. No failed official SDK\nexport occurred in this study.\n\nThe0.4.0wheel was built offline with setuptools80.9.0/wheel0.45.1, then installed\nand replayed in isolated Python outside Git and the checkout with Git absent\nfrom PATH. All64 trusted source bytes match. Original ReLU/GEMV/GEMM/BMM source\nand Main bytes and frozen0.1/0.2/0.3wheels remain unchanged. Enlarged current\nrosters refuse earlier recordings before output; exact old source pins remain\nrequired. No legacy profile or model success is registered.\n\nThe abstract scalar correspondence, Python parsing/reference formalization,\nlogical pointer provenance and aligned disjoint non-wrapping allocations remain\ntrusted. This establishes no IEEE/error bound, PyTorch or NVIDIA conformance,\nNVIDIA execution, original optimized program, original model result or full\npaper reproduction. No model or GPU trial was performed for this proof study.\n\nSeven deterministic archives retain all official recordings, installed package\nvalidation, wheel, SDK test logs and complete retained development history.\nEvery member has a SHA256 inventory and a round-trip check. Limits remain180s\nper Lean process,600s per source-import aggregate, maxRecDepth10000 and\nmaxHeartbeats2000000; legacy source limits are unchanged. Publication/actual CI\nare separately gated. See [the checker commands](../../LINEAR.md).\n")
    write(ROOT / 'dedicated-replay-environment.json', {
        'kind': 'recorded-tool-invocation-observation-not-a-new-replay', 'tool_session': 57741,
        'terminal_exit_code': 0, 'cwd': '/tmp', 'PATH': '/nonexistent', 'PYTHONPATH': str(REPO),
        'trusted_SDK_loaded_from_current_source': True, 'captured_Python_executed': False,
        'git_on_PATH': False, 'installed_wheel_isolation_recorded_separately': True})
    write(ROOT / 'local-test-terminal-observations.json', {
        'kind': 'terminal-observations-not-new-tests', 'reader_regression_tests': 24,
        'reader_regression_seconds': 1.266, 'reader_regression_exit': 0,
        'SDK_integration_session': 45860, 'SDK_integration_exit': 0,
        'SDK_integration_seconds': tests['seconds'], 'model_calls': 0, 'gpu_trials': 0})
    write(ROOT / 'manifest.json', inventory(ROOT))
    print(json.dumps({'status': result['status'], 'output': str(ROOT), 'archives': len(archives),
        'archive_members': sum(v['files'] for v in archives.values()), 'files': len(list(ROOT.iterdir())),
        'bytes': sum(p.stat().st_size for p in ROOT.iterdir()), 'manifest_sha256': sha(ROOT / 'manifest.json')}), flush=True)


if __name__ == '__main__':
    main()
