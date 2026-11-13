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

ROOT = Path('/tmp/lark-ptx-pointwise-proof-packet-v1-20261113')
REPO = Path('/tmp/lark-ptx-pointwise-refinement-20261113')
PRODUCER = '502f94c0bf845615aad06abdd099e7052f2e82cf'
SOURCES = {
    'export': Path('/tmp/lark-ptx-pointwise-source-export-v1-20261113'),
    'replay': Path('/tmp/lark-ptx-pointwise-source-replay-v1-20261113'),
    'controls': Path('/tmp/lark-ptx-pointwise-source-controls-v1-20261113'),
    'installed-wheel': Path('/tmp/lark-ptx-pointwise-wheel-validation-v1-20261113'),
    'wheel-build': Path('/tmp/lark-ptx-pointwise-wheel-v2-20261113'),
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
        require(report['status'] == 'verified-source-bound-finite-PTX'
                and report['source_bound_proof_accepted'] is True
                and report['elements'] == 16384 and report['PTX_instructions'] == 15
                and report['launch'] == {'grid': 16384, 'block': 1, 'warp': 32}
                and report['unchanged_CUDA_contract_fuel'] == [4, 1, 1, 1]
                and report['main_sha256'] == original['main_sha256'] == sha(root / 'Main.lean')
                and report['input_bindings'] == original['input_bindings']
                and report['owned_Lean_modules_freshly_compiled'] == 3
                and report['old_owned_olean_cache_used'] is False
                and len(report['axiom_audits']) == 6
                and len(report['library_axiom_audits']) == 22
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
    controls = read(SOURCES['controls'] / 'results.json')
    require(controls['status'] == 'full-size-PTX-ReLU-source-controls-passed'
            and controls['positive_controls'] == 1 and controls['direct_Lean_negative_controls'] == 4
            and controls['timeouts'] == 0
            and all(c['reader_accepted'] is True and c['Lean']['exit_code'] != 0
                    and c['Lean']['timed_out'] is False
                    and c['channel'] == 'source-program-equality-proof-refused'
                    for c in controls['negative_controls']), 'Four direct Lean controls required')
    installed = read(SOURCES['installed-wheel'] / 'results.json')
    wheel = SOURCES['wheel-build'] / 'lark_kernels-0.1.0-py3-none-any.whl'
    require(installed['status'] == 'installed-wheel-source-only-replay-passed'
            and installed['exit_code'] == 0 and installed['checkout_imported'] is False
            and installed['isolated_mode'] is True
            and installed['network_during_install_and_replay'] is False
            and installed['wheel_sha256'] == sha(wheel), 'Isolated installed-wheel replay required')
    ROOT.mkdir()
    archives = {label: archive(label, source) for label, source in SOURCES.items()}
    for source, name in [(export / 'results.json', 'proof-results.json'),
                         (SOURCES['replay'] / 'replay.json', 'replay-results.json'),
                         (SOURCES['controls'] / 'results.json', 'controls-results.json'),
                         (SOURCES['installed-wheel'] / 'results.json', 'installed-wheel-results.json'),
                         (Path('/tmp/lark-ptx-pointwise-wheel-v1-20261113/failure.json'),
                          'initial-build-backend-failure.json')]:
        shutil.copyfile(source, ROOT / name)
    result = {
        'schema': 1, 'status': 'exact-source-full-size-PTX-ReLU-proof-evidence',
        'packaged_at_utc': datetime.now(timezone.utc).isoformat(),
        'producer_commit': PRODUCER, 'profile': original['profile'],
        'independent_source_bound_development_proofs': 1,
        'retained_positive_Main_checks': 4, 'positive_rechecks': 3,
        'owned_module_builds_across_four_checks': 12,
        'direct_Lean_negative_controls': 4, 'negative_timeouts': 0,
        'elements': 16384, 'dtype': 'float16', 'PTX_instructions': 15,
        'launch': original['launch'], 'unchanged_CUDA_contract_fuel': [4, 1, 1, 1],
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
    (ROOT / 'RESULTS.md').write_text('''# Exact-source full-size FP16 PTX ReLU proof

One independent 16,384-element FP16 ReLU program now has a source-bound Lean
proof through a separate finite PTX checker. It parses the actual 15-instruction
PTX 8.8/sm_80 compiler output from the CPU assembly study. Input source,
reference, task, shape, dtype, grid (16,384), block (one thread), warp (32),
and original CUDA contract fuel [4,1,1,1] are unchanged. The structurally finite
PTX interpreter executes all 15 instructions; CUDA fuel is a separate model's
contract data and does not limit this PTX interpreter to four instructions.

The immutable Main binds the actual parsed instruction list and closed reference
AST in Lean, then proves whole-launch completion, race freedom for actual memory
events, segment equivalence and every reference output. Source-language PTX and
reference-contract-language CUDA are recorded separately. There is no captured
proof proposal or model call in this study.

The original export and three rechecks (dedicated source-only replay, controls'
positive replay, and an isolated installed-wheel replay) all passed. Each builds
three owned Lean modules from trusted source, for 12 module builds and four
positive Main checks total. These are repeated checks of ONE kernel. Each Main
has six axiom audits and the PTX library has 22. All use only the standard Lean
axioms propext, Classical.choice and Quot.sound. No old owned olean cache is used.

Four source mutations pass the reader and fail directly in Lean at the fixed
profile's source-program equality proof: wrong arithmetic, misaligned byte
stride, wrong output address and skipped half conversion. None times out. These
check source binding; they are not a general kernel-falsity classifier or the
paper's original 42 mutants.

The wheel was built using an isolated compatible backend (setuptools 80.9.0,
wheel 0.45.1), installed offline without dependencies into a fresh venv, then
replayed with Python isolated mode outside the checkout. Its source bindings and
Main match the export. The first build's incompatible system-backend failure is
retained separately; no project license or proof limit was changed to bypass it.

All floating operations have the declared abstract scalar semantics. The reader,
reference formalization, scalar-operation/ABI correspondence and aligned,
disjoint, non-wrapping host allocation assumptions remain trusted. This does not
establish IEEE/error-bound equivalence, NVIDIA execution/conformance, an original
optimized kernel, or an original model/table result. The separate development
checker registers no new legacy SDK certificate profile. Existing HIP/CUDA model
cohort results are unchanged. Other full-size PTX families remain unfinished.

`export.tar.gz`, `replay.tar.gz`, `controls.tar.gz`, `installed-wheel.tar.gz` and
`wheel-build.tar.gz` preserve exact source/contract/reference bytes, immutable
Main, translations, source identities, module sources, captured oleans, logs,
toolchain/axiom/resource checks, mutation inputs and installed-wheel receipts.
Each archive has a complete file/hash inventory and was round-trip checked.
Captured Python, Lean and oleans are data during source-only replay; trusted
current source is checked and compiled afresh. See ../../POINTWISE.md for commands.
''')
    write(ROOT / 'manifest.json', inventory(ROOT))
    print(json.dumps({'output': str(ROOT), 'files': len(list(ROOT.iterdir())),
                      'bytes': sum(p.stat().st_size for p in ROOT.iterdir()),
                      'manifest_sha256': sha(ROOT / 'manifest.json')}))


if __name__ == '__main__':
    main()
