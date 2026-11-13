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

ROOT = Path('/tmp/lark-ptx-dot-proof-packet-v1-20261113')
REPO = Path('/tmp/lark-ptx-dot-refinement-20261113')
PRODUCER = '769e6deebc4d19415d787360d2a5ed5e57c516fd'
SOURCES = {
    'export': Path('/tmp/lark-ptx-dot-source-export-v1-20261113'),
    'replay': Path('/tmp/lark-ptx-dot-source-replay-v1-20261113'),
    'controls': Path('/tmp/lark-ptx-dot-source-controls-v1-20261113'),
    'installed-wheel': Path('/tmp/lark-ptx-dot-wheel-validation-v1-20261113'),
    'wheel-build': Path('/tmp/lark-ptx-dot-wheel-v1-20261113'),
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
        require(report['status'] == 'verified-source-bound-full-PTX-GEMV'
                and report['source_bound_proof_accepted'] is True
                and report['shapes'] == [[512, 1024], [1024, 1], [512, 1]]
                and report['dtypes'] == ['float16', 'float16', 'float16'] and report['PTX_instructions'] == 119
                and report['launch'] == {'grid': 512, 'block': 1, 'warp': 32}
                and report['unchanged_CUDA_contract_fuel'] == [4102, 1, 1, 1]
                and report['main_sha256'] == original['main_sha256'] == sha(root / 'Main.lean')
                and report['input_bindings'] == original['input_bindings']
                and type(report['owned_Lean_modules_freshly_compiled']) is int
                and report['owned_Lean_modules_freshly_compiled'] == 4
                and report['old_owned_olean_cache_used'] is False
                and len(report['axiom_audits']) == 6
                and len(report['library_axiom_audits']) == 102
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
    require(original['input_bindings'] == {'kernel.ptx': '79afeb989948bd8e36278f7b12836e1920727197d6662ddf8b1a642a53a1354c',
            'reference.py': 'f5ef4b758351b5b73d77a49f066383c93324cc39f8d44d183480864f46336f6f',
            'contract.json': '2cd47c1c652ddad9b4ea027bf1c4523c3b8cc72c28f04684a1d906eeeba1ce71'},
            'Exact full-size compiler-study inputs required')
    controls = read(SOURCES['controls'] / 'results.json')
    require(controls['status'] == 'full-size-PTX-GEMV-source-controls-passed'
            and controls['positive_controls'] == 1 and controls['direct_Lean_negative_controls'] == 4
            and controls['timeouts'] == 0
            and all(c['reader_accepted'] is True and c['Lean']['exit_code'] != 0
                    and c['Lean']['timed_out'] is False
                    and c['channel'] == 'source-program-equality-proof-refused'
                    for c in controls['negative_controls']), 'Four direct Lean controls required')
    installed = read(SOURCES['installed-wheel'] / 'results.json')
    wheel = SOURCES['wheel-build'] / 'lark_kernels-0.1.0-py3-none-any.whl'
    require(installed['status'] == 'installed-wheel-source-only-PTX-GEMV-replay-passed'
            and installed['exit_code'] == 0 and installed['checkout_imported'] is False
            and installed['isolated_mode'] is True
            and installed['network_during_install_and_replay'] is False
            and installed['git_on_PATH'] is False and installed['all_owned_source_bindings_match'] is True
            and installed['legacy_ReLU_owned_source_bindings_match'] is True
            and installed['legacy_ReLU_Main_regenerated_identically'] is True
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
        'schema': 1, 'status': 'exact-source-full-size-PTX-GEMV-proof-evidence',
        'packaged_at_utc': datetime.now(timezone.utc).isoformat(),
        'producer_commit': PRODUCER, 'profile': original['profile'],
        'independent_source_bound_development_proofs': 1,
        'retained_positive_Main_checks': 4, 'positive_rechecks': 3,
        'owned_module_builds_across_four_checks': 16,
        'direct_Lean_negative_controls': 4, 'negative_timeouts': 0,
        'shapes': [[512, 1024], [1024, 1], [512, 1]], 'dtype': 'float16', 'PTX_instructions': 119,
        'library_axiom_audits_per_check': 102, 'Main_axiom_audits_per_check': 6,
        'launch': original['launch'], 'unchanged_CUDA_contract_fuel': [4102, 1, 1, 1],
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
    (ROOT / 'RESULTS.md').write_text("# Exact-source full-size FP16 PTX GEMV proof\n\nOne independent 512×1024 FP16 matrix-vector program has a source-bound Lean\nproof through a separate development checker. The actual NVRTC 12.9.86 PTX\n8.8/sm_80 output contains 119 instructions. Matrix [512,1024], vector [1024,1],\noutput [512,1], all FP16 dtypes, grid 512, block one, warp 32 and the original\nCUDA contract fuel [4102,1,1,1] remain unchanged.\n\nThe immutable Main binds the complete parsed instruction list and independently\nclosed reference AST. Lean checks the twelve-instruction prologue, all 64\nsixteen-term iterations, actual pointer/counter/predicate/backward-branch control,\noutput store and ret. The complete-launch theorem covers all 512 active lanes,\nrace freedom of the actual recorded memory events, and every extracted output\nagainst the ordered 1,024-term interpretation of `(a.float() @ b.float()).half()`.\nFinite successful instruction transitions establish execution without a new fuel\nor an assumed loop summary. CUDA fuel is data for its separate model.\n\nFour retained positive Main checks passed: original SDK export, dedicated\noutside-checkout/no-Git replay, the controls' fresh positive replay, and isolated\ninstalled-wheel replay. Each rebuilds all four owned Lean modules from trusted\nsource, for 16 module builds, 102 library axiom audits and six Main audits per\ncheck. Only propext, Classical.choice and Quot.sound occur. No old owned olean\ncache is used. These are repeated checks of ONE independent development kernel.\n\nFour accepted-grammar source mutations fail directly in Lean at source_program:\nwrong product, wrong loop-counter stride, premature loop exit and conflicting\noutput address. None times out. They preserve all task/launch/fuel data. These\nare source-binding controls, not general false-kernel classification or the\npaper's original 42 mutants.\n\nThe wheel was built offline with setuptools 80.9.0 and wheel 0.45.1, installed\nwithout dependencies, and replayed with Python isolated mode outside the checkout\nand with Git absent from PATH. All source identities and the Main match. The\nprevious ReLU profile's owned-source bindings and regenerated Main also remain\nbyte-identical; that compatibility check adds no new ReLU proof or GPU trial.\n\nThe proof uses declared abstract scalar semantics. Parsing/reference\nformalization, logical pointer provenance, scalar-operation correspondence and\naligned disjoint non-wrapping host allocations remain trusted. It establishes no\nIEEE rounding/error bound, PyTorch backend equivalence, NVIDIA execution or\nconformance, original optimized kernel, original model result or paper table.\nNo new legacy SDK profile is registered, no model call or GPU experiment was\nperformed, and the six fixed-scaffold model cohorts remain unchanged. Other\nfull-size PTX families and original artifacts remain unfinished or unavailable.\n\nFive deterministic archives preserve the actual export, replay, controls,\ninstalled-wheel validation and wheel build. Each has a complete hash inventory\nand was round-trip checked. Captured Python/Lean/oleans are data; replay checks\nmatched current trusted source, builds all four owned modules in one fresh import\nroot, and regenerates and checks the same Main. Resource limits remain\nmaxRecDepth 10000, maxHeartbeats 2000000, 180 seconds per Lean process and 600\nseconds per source-import aggregate; legacy libraries retain their source limits.\nSee [the development checker commands](../../DOT.md).\n")
    write(ROOT / 'manifest.json', inventory(ROOT))
    print(json.dumps({'output': str(ROOT), 'files': len(list(ROOT.iterdir())),
                      'bytes': sum(p.stat().st_size for p in ROOT.iterdir()),
                      'manifest_sha256': sha(ROOT / 'manifest.json')}))


if __name__ == '__main__':
    main()
