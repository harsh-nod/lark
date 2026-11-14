"""Archive retained RoPE evidence without running Lean, models or GPU work."""

from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
import math
from pathlib import Path
import re
import subprocess
import sys
import tarfile
import zipfile

REPO = Path('/tmp/lark-ptx-rotary-refinement-20261113')
OUT = Path('/tmp/lark-ptx-rotary-proof-packet-v1-20261113')
PRODUCER = '538500cbb1a0374f798eded3a83199bbf630ada6'
WHEEL_PRODUCER = '20e4605ebf7de7254fb121d00f9e9e5bd9042615'
sys.path.insert(0, str(REPO))
from lark_kernels import ptx_rotary as reader
from lark_kernels import ptx_rotary_certificate as sdk


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def files(root):
    return {p.relative_to(root).as_posix(): p for p in sorted(root.rglob('*')) if p.is_file()}


def inventory(paths):
    return {n: sha(p.read_bytes()) for n, p in paths.items()}


def checked(root):
    paths = files(root)
    require({n: h for n, h in inventory(paths).items() if n != 'manifest.json'}
            == read(root / 'manifest.json'), 'Changed recording: ' + str(root))
    return paths


def positive(root):
    checked(root)
    proof = read(root / 'results.json')
    sources = sdk.own_sources()
    require(len(sources) == 64 and sum(n.startswith('python/') for n in sources) == 56,
            'Full 56 Python + 8 Lean source roster')
    for n, data in sources.items():
        path = 'lark_kernels/' + n[7:] if n.startswith('python/') else n
        require(subprocess.check_output(['git', 'show', PRODUCER + ':' + path], cwd=REPO) == data
                == (root / 'owned-sources' / n).read_bytes(), 'Producer/current/captured source: ' + n)
    require(read(root / 'source-bindings.json') == {n: sha(v) for n, v in sources.items()},
            'All 64 source bindings')
    inputs = {n: (root / n).read_bytes() for n in sdk.INPUTS}
    prepared = reader.prepare_certificate(*(inputs[n].decode() for n in sdk.INPUTS))
    require(sdk.same_json({k: proof[k] for k in sdk.scope_fields(*prepared[:2])},
                         sdk.scope_fields(*prepared[:2]))
            and (root / 'Main.lean').read_bytes() == reader.render(*prepared).encode()
            and sdk.same_json(read(root / 'translation.json'), prepared[1].data())
            and sdk.same_json(read(root / 'reference-ast.json'), prepared[2]), 'Actual full source/reference rendering')
    expected = sdk.expected_paths(sources)
    if (root / 'replay.json').exists():
        expected |= {'replay.json', 'proof-export-manifest.json'}
    require(set(read(root / 'manifest.json')) == expected, 'Exact positive roster')
    require(proof['status'] == 'verified-source-bound-full-PTX-ROTARY'
            and proof['profile'] == reader.PROFILE and proof['scope'] == sdk.SCOPE
            and proof['source_bound_proof_accepted'] is True
            and proof['old_owned_olean_cache_used'] is False
            and proof['nvidia_execution'] is proof['original_paper_fully_reproduced'] is False
            and all(type(proof[k]) is int and proof[k] == v for k, v in {
                'source_bound_development_proofs': 1, 'owned_Lean_modules_freshly_compiled': 8,
                'model_calls': 0, 'gpu_trials': 0, 'new_registered_source_certificates': 0}.items())
            and sdk.same_json(proof['limits'], sdk.LIMITS)
            and proof['lean_binary_sha256'] == sdk.LEAN_SHA256
            and proof['input_bindings'] == {n: sha(v) for n, v in inputs.items()}
            and proof['main_sha256'] == sha((root / 'Main.lean').read_bytes())
            and proof['source_bindings_sha256'] == sha((root / 'source-bindings.json').read_bytes())
            and proof['reference_ast_sha256'] == sha((root / 'reference-ast.json').read_bytes()), 'Positive scope')
    main_audits = sdk.common.audits((root / 'Main.log').read_text(),
                                  ['LarkPtxRotaryCertificate.' + n for n in reader.TAGS])
    require(len(main_audits) == 7 and main_audits == proof['axiom_audits']
            and sdk.valid_check(proof['main_check'], (root / 'Main.log').read_bytes(), ['Main.lean']),
            'Actual accepted Main log/audit/budget')
    require([r['module'] for r in proof['module_checks']] == ['Lark.' + n for n in sdk.MODULES],
            'Eight fresh module checks')
    library = {}
    for module, row in zip(sdk.MODULES, proof['module_checks'], strict=True):
        log = (root / (module + '.log')).read_bytes()
        require(sdk.valid_check(row, log, ['-o', 'Lark/' + module + '.olean', 'Lark/' + module + '.lean'])
                and (root / 'modules/Lark' / (module + '.lean')).read_bytes()
                == sources['lean/Lark/' + module + '.lean'], 'Fresh module source/log/budget')
        library.update(sdk.common.audits(log.decode(), sdk.library_tags(sources, module)))
    require(len(library) == 265 and proof['library_axiom_audits'] == library
            and type(proof['import_build_seconds']) in (int, float)
            and math.isfinite(proof['import_build_seconds']) and 0 <= proof['import_build_seconds'] <= 600,
            'Library audits/aggregate budget')
    return proof


def archive(label, paths, group):
    paths = dict(sorted(paths.items()))
    inv = inventory(paths)
    write(OUT / (label + '-files.json'), inv)
    target = OUT / (label + '.tar.gz')
    with target.open('wb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0,
                                               compresslevel=9) as zipped, \
            tarfile.open(fileobj=zipped, mode='w') as tar:
        for n, p in paths.items():
            data = p.read_bytes()
            item = tarfile.TarInfo(n)
            item.size, item.mode, item.mtime = len(data), 0o644, 0
            require(sha(data) == inv[n], 'Source changed while archiving')
            tar.addfile(item, io.BytesIO(data))
    seen, size = set(), 0
    with tarfile.open(target, mode='r|gz') as tar:
        for member in tar:
            require(member.isfile() and member.name not in seen and member.name in inv,
                    'Archive member roster/type')
            require(sha(tar.extractfile(member).read()) == inv[member.name], 'Archive round-trip bytes')
            seen.add(member.name)
            size += member.size
    require(seen == set(inv) and size <= 90_000_000 and target.stat().st_size <= 90_000_000,
            'Archive roster/bound')
    print(json.dumps({'archive': label, 'files': len(inv), 'bytes': target.stat().st_size}), flush=True)
    return {'group': group, 'files': len(inv), 'uncompressed_bytes': size,
            'archive_bytes': target.stat().st_size, 'archive_sha256': sha(target.read_bytes()),
            'inventory_sha256': sha((OUT / (label + '-files.json')).read_bytes())}


def groups(roots, prefix):
    batches, current, size = [], {}, 0
    for name, root in roots:
        paths = checked(root)
        amount = sum(p.stat().st_size for p in paths.values())
        if current and size + amount > 90_000_000:
            batches.append(current)
            current, size = {}, 0
        current.update({name + '/' + n: p for n, p in paths.items()})
        size += amount
    if current:
        batches.append(current)
    return {prefix + '-' + str(i + 1): batch for i, batch in enumerate(batches)}


def main():
    require(not OUT.exists(), 'Inspect existing packaging observer/output instead of restarting')
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip() == WHEEL_PRODUCER
            and not subprocess.check_output(['git', 'status', '--porcelain'], cwd=REPO), 'Clean bound producer')
    state = read(Path('/tmp/lark-awq-native-handoff-20261112.json'))['ptx_rotary_refinement_draft']
    positive_roots = dict(zip(('export', 'replay-v1', 'replay-v2', 'wheel-replay'),
                              (Path(r['path']) for r in state['four_current_positive_checks']), strict=True))
    proofs = {label: positive(root) for label, root in positive_roots.items()}
    require(len({p['main_sha256'] for p in proofs.values()}) == 1, 'Identical regenerated Main')
    controls_root = Path(state['direct_Lean_controls']['path'])
    direct_paths, direct = checked(controls_root), read(controls_root / 'results.json')
    require(direct['negative_controls'] == 4 and direct['negative_timeouts'] == direct['resource_limit_failures'] == 0
            and all(r['expected_rejection_verified'] is True for r in direct['controls']), 'Four actual refusals')
    rehashed_root = Path(state['rehashed_controls']['path'])
    checked(rehashed_root)
    rehashed = read(rehashed_root / 'results.json')
    require(rehashed['negative_controls'] == 17 and rehashed['fresh_Lean_checks'] == 0
            and all(r['status'] == 'rejected-before-fresh-Lean-work' and r['output_created'] is False
                    for r in rehashed['checks']), '17 coherent refusals')
    attempts = sorted(state['development_attempts'], key=lambda r: int(re.search(r'-v(\d+)-', r['path'])[1]))
    require(len(attempts) == 17 and sum(r['check']['exit_code'] == 0 for r in attempts) == 6,
            'All 17 development attempts, 6 passed / 11 failed')
    installed_root, wheel_root = Path(state['installed_wheel']['path']), Path(state['wheel']['path'])
    installed_paths, wheel_paths = checked(installed_root), checked(wheel_root)
    installed, build = read(installed_root / 'results.json'), read(wheel_root / 'build-results.json')
    wheel = wheel_root / build['wheel_filename']
    require(build['exit_code'] == 0 and build['source_commit'] == WHEEL_PRODUCER
            and installed['status'] == 'installed-wheel-outside-Git-full-RoPE-replay-passed'
            and sha(wheel.read_bytes()) == build['wheel_sha256'] == installed['wheel_sha256'], 'Wheel evidence')
    with zipfile.ZipFile(wheel) as zipped:
        for n, data in sdk.own_sources().items():
            key = 'lark_kernels/' + n[7:] if n.startswith('python/') else next(
                p for p in zipped.namelist() if p.endswith('/share/lark/' + n))
            require(zipped.read(key) == data, 'Wheel source bytes')
    OUT.mkdir()
    (OUT / 'packaging-driver.py').write_bytes(Path(__file__).read_bytes())
    links = {p.relative_to(installed_root).as_posix(): str(p.readlink())
             for p in sorted(installed_root.rglob('*')) if p.is_symlink()}
    write(OUT / 'runtime-links.json', {'encoding': 'File-symlink contents archived as regular data; original link targets retained here. Directory links retained as metadata. No captured code executed.',
                                      'installed-wheel': links})
    archives = {label: archive(label, checked(root), 'positive') for label, root in positive_roots.items()}
    archives['direct-controls'] = archive('direct-controls', direct_paths, 'direct-controls')
    case_roots = [(r['name'], rehashed_root / r['name']) for r in rehashed['checks']]
    batches = groups(case_roots, 'rehashed-controls')
    batches['rehashed-metadata'] = {n: p for n, p in files(rehashed_root).items() if '/' not in n}
    for label, paths in batches.items():
        archives[label] = archive(label, paths, 'rehashed-controls')
    for label, paths in groups([(Path(r['path']).name, Path(r['path'])) for r in attempts], 'development').items():
        archives[label] = archive(label, paths, 'development')
    preparation_roots = [Path(state['preparation']), Path(state['foundation_commit_receipt']),
                         Path(state['reader_tests']['output']), Path(state['reader_validation_v2']['path']),
                         Path(state['instruction_build']['output']),
                         Path(state['official_export_observer']['path']),
                         Path(state['two_source_replays_observer']['path']),
                         Path(state['failed_wheel_preflight']['path'])]
    preparation = {root.name + '/' + n: p for root in preparation_roots for n, p in checked(root).items()}
    archives['preparation-history'] = archive('preparation-history', preparation, 'preparation')
    archives['wheel-build'] = archive('wheel-build', wheel_paths, 'wheel')
    archives['installed-wheel'] = archive('installed-wheel', installed_paths, 'installed')
    for label, proof in proofs.items():
        write(OUT / (label + '-results.json'), proof)
    for label, data in [('direct-controls', direct), ('rehashed-controls', rehashed),
                        ('wheel-build', build), ('installed-wheel', installed)]:
        write(OUT / (label + '-results.json'), data)
    history = {'attempts': attempts, 'all_payloads_preserved': True,
               'cached_development_counts_as_source_only_export': False,
               'failed_Lean_drafts_never_accepted': True, 'passed': 6, 'failed': 11,
               'failed_wheel_preflight_retained': str(preparation_roots[-1]),
               'failed_official_exports': 0}
    write(OUT / 'validation-history.json', history)
    first = proofs['export']
    report = {'schema': 1, 'status': 'complete-full-size-PTX-ROTARY-proof-evidence-retained',
              'packaged_at_utc': datetime.now(timezone.utc).isoformat(),
              'SDK_source_commit': PRODUCER, 'wheel_source_commit': WHEEL_PRODUCER,
              'packaging_driver_sha256': sha(Path(__file__).read_bytes()),
              'profile': reader.PROFILE, 'scope': sdk.SCOPE,
              'independent_source_bound_development_proofs': 1, 'retained_positive_Main_checks': 4,
              'positive_rechecks': 3, 'fresh_owned_module_builds': 32,
              'direct_Lean_negative_controls': 4, 'coherently_rehashed_negative_controls': 17,
              'development_attempts': 17, 'passed_development_checks': 6, 'failed_development_checks': 11,
              'retained_failed_official_exports': 0, 'owned_source_files': 64, 'Python_files': 56, 'Lean_files': 8,
              'PTX_instructions': 51, 'registers': 52, 'active_lanes': 32768,
              'actual_instructions_per_lane': 41, 'actual_accesses_per_lane': 5,
              'library_axiom_audits_per_check': 265, 'Main_axiom_audits_per_check': 7,
              'model_calls': 0, 'gpu_trials': 0, 'new_registered_source_certificates': 0,
              'nvidia_execution': False, 'original_paper_fully_reproduced': False,
              'all_payloads_and_failed_history_retained': True, 'captured_code_executed_by_packager': False,
              'wheel_sha256': sha(wheel.read_bytes()), 'archives': archives}
    for key in ['shapes', 'launch', 'unchanged_CUDA_contract_fuel', 'limits', 'input_bindings',
                'lean_binary_sha256', 'main_sha256', 'source_bindings_sha256', 'reference_ast_sha256']:
        report[key] = first[key]
    write(OUT / 'results.json', report)
    (OUT / 'RESULTS.md').write_text('''# Full-size compiled interleaved RoPE development proof

One independent source-bound abstract PTX proof, four retained fresh checks,
32 fresh owned module builds, three rechecks, four direct Lean refusals and
17 coherently rehashed SDK recording refusals. All 17 earlier development
attempts (six passing partial checks, eleven failures), preparation and the
failed wheel preflight are retained in full with their original manifests.
No failed or partial check is counted as an official positive proof.

The unchanged FP16 shapes are x/out[256,128] and cosine/sine[256,64], with
grid 32768, block 1, warp 32 and original CUDA fuel [8,1,1,1]. All 51 source
instructions and 52 physical registers are retained. Each lane executes its
actual 41-instruction path, with five memory accesses. The full launch has
race-free access traces, preserves memory outside the output and matches an
independent shape-checked reshape/select/stack/arithmetic/half tensor denotation.

These are recorded checks; archive validation runs no Lean, model or GPU.
The installed environment is retained completely. Its file symlinks are
archived as ordinary byte data, and all original link targets, including the
directory link, are recorded in runtime-links.json. Captured code is data.
No proof limit, original shape, geometry or fuel was increased or reduced.

The proof uses abstract scalar operations and trusted parsing, ABI/pointer
correspondence and aligned disjoint non-wrapping allocations. It establishes
no IEEE/error bound, NVIDIA execution/conformance, original optimized-kernel
result, model success, legacy profile registration or full-paper reproduction.
Anonymous public verification and source CI remain separate publication gates.
''')
    write(OUT / 'manifest.json', inventory({n: p for n, p in files(OUT).items() if n != 'manifest.json'}))
    write(OUT.with_suffix('.complete.json'), {'status': 'complete', 'packet': str(OUT),
          'manifest_sha256': sha((OUT / 'manifest.json').read_bytes()), 'archives': len(archives),
          'members': sum(r['files'] for r in archives.values()), 'model_calls': 0, 'gpu_trials': 0})
    print(OUT.with_suffix('.complete.json').read_text(), flush=True)


if __name__ == '__main__':
    main()
