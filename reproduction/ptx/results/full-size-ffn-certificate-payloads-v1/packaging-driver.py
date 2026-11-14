"""Package complete retained FFN certificate payloads; execute no captured code."""
from pathlib import Path, PurePosixPath
import gzip
import hashlib
import io
import json
import subprocess
import sys
import tarfile

ROOT = Path('/tmp/lark-ptx-ffn-refinement-20261114')
OUT = Path('/tmp/lark-ffn-certificate-payloads-v1-20261114')
PRODUCER = 'f49adeb6472a163b58e209e0ec62646b2f23c75f'
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_ffn_certificate as checker


def files(root):
    paths = {}
    for p in sorted(root.rglob('*')):
        assert not p.is_symlink(), str(p)
        if p.is_file():
            paths[p.relative_to(root).as_posix()] = p
    return paths


def checked(root):
    checker.check_inventory(root)
    return files(root)


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def archive(label, paths, group):
    paths = dict(sorted(paths.items()))
    inventory = {n: {'bytes': p.stat().st_size, 'sha256': digest(p)} for n, p in paths.items()}
    checker.write(OUT / (label + '-files.json'), inventory)
    size = sum(r['bytes'] for r in inventory.values())
    assert size <= 85_000_000 and all(r['bytes'] <= 10_000_000 for r in inventory.values())
    path = OUT / (label + '.tar.gz')
    with path.open('xb') as raw, gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0, compresslevel=9) as compressed, tarfile.open(fileobj=compressed, mode='w') as stream:
        for name, source in paths.items():
            data = source.read_bytes()
            assert len(data) == inventory[name]['bytes'] and checker.sha(data) == inventory[name]['sha256']
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.mtime = len(data), 0o644, 0
            stream.addfile(info, io.BytesIO(data))
    seen = set()
    with tarfile.open(path, 'r|gz') as stream:
        for member in stream:
            n = member.name
            assert member.isfile() and n in inventory and n not in seen
            assert str(PurePosixPath(n)) == n and not PurePosixPath(n).is_absolute() and '..' not in PurePosixPath(n).parts
            data = stream.extractfile(member).read()
            assert member.size == len(data) == inventory[n]['bytes'] and checker.sha(data) == inventory[n]['sha256']
            seen.add(n)
    assert seen == set(inventory) and path.stat().st_size <= 90_000_000
    result = {'group': group, 'files': len(inventory), 'uncompressed_bytes': size,
              'archive_bytes': path.stat().st_size, 'archive_sha256': digest(path),
              'inventory_sha256': digest(OUT / (label + '-files.json'))}
    print(json.dumps({'archive': label, **result}), flush=True)
    return result


def main():
    assert not OUT.exists(), 'Inspect original packaging process/output before any new launch'
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip() == '7fcd17c0f1c8558737783be69a8c6fb503c16e6f'
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip()
    sources = checker.own_sources()
    assert len(sources) == 72
    for n, data in sources.items():
        path = 'lark_kernels/' + n.removeprefix('python/') if n.startswith('python/') else n
        assert data == subprocess.check_output(['git','show',PRODUCER + ':' + path],cwd=ROOT)
    export = Path('/tmp/lark-ptx-ffn-certificate-export-v1-20261114')
    direct = Path('/tmp/lark-ptx-ffn-source-controls-v1-20261114')
    false = Path('/tmp/lark-ptx-ffn-recording-controls-v1-20261114')
    wheel = Path('/tmp/lark-ptx-ffn-wheel-v1-20261114')
    positives = [export, direct/'positive-source-only-replay', wheel/'fresh-installed-replay']
    for p in positives:
        checker.check_inventory(p)
        r = checker.read(p/'results.json')
        assert r['status'] == checker.VERIFIED and r['source_bound_proof_accepted'] is True
        assert r['original_stack_limits'] == [8388608,-1]
        assert r['owned_Lean_modules_freshly_compiled'] == 14 and r['old_owned_olean_cache_used'] is False
        assert len(r['axiom_audits']) + len(r['library_axiom_audits']) == 256
        assert checker.read(p/'source-bindings.json') == {n: checker.sha(v) for n,v in sources.items()}
    controls = checker.read(direct/'results.json')
    assert controls['direct_Lean_negative_controls'] == 4
    assert all(r['expected_rejection_verified'] is True and r['resource_failure'] is False and r['Lean']['timed_out'] is False for r in controls['negative_controls'])
    checker.check_inventory(false)
    forged = checker.read(false/'results.json')
    assert forged['negative_controls'] == 31 and forged['fresh_Lean_checks'] == 0
    assert all(r['status'] == 'rejected-before-fresh-Lean-work' and r['output_created'] is False for r in forged['checks'])
    wheel_manifest = checker.read(wheel/'manifest.json')
    wheel_files = {n: wheel/n for n in wheel_manifest}
    assert all(p.is_file() and not p.is_symlink() and digest(p) == wheel_manifest[n] for n,p in wheel_files.items())
    assert all(PurePosixPath(n).parts[0] != 'venv' for n in wheel_files)
    OUT.mkdir()
    (OUT/'packaging-driver.py').write_bytes(Path(__file__).read_bytes())
    archives = {'export': archive('export', checked(export), 'positive'),
                'source-controls-and-fresh-replay': archive('source-controls-and-fresh-replay', checked(direct), 'direct-controls'),
                'installed-wheel-and-fresh-replay': archive('installed-wheel-and-fresh-replay', wheel_files, 'installed-wheel')}
    batch, amount, number = {}, 0, 0
    for row in forged['checks']:
        paths = checked(false/row['name'])
        size = sum(p.stat().st_size for p in paths.values())
        if batch and amount + size > 85_000_000:
            number += 1; label = f'false-recordings-{number:02d}'
            archives[label] = archive(label, batch, 'rehashed-controls')
            batch, amount = {}, 0
        batch.update({row['name']+'/'+n: p for n,p in paths.items()})
        amount += size
    if batch:
        number += 1; label = f'false-recordings-{number:02d}'
        archives[label] = archive(label, batch, 'rehashed-controls')
    archives['false-recordings-metadata'] = archive('false-recordings-metadata', {p.name:p for p in false.iterdir() if p.is_file()}, 'rehashed-controls')
    report = {'schema':1,'status':'complete-current-FFN-certificate-payloads-packaged-and-byte-checked',
              'SDK_producer_commit':PRODUCER,'scope':checker.SCOPE,'archives':archives,
              'complete_original_positive_checks':3,'direct_Lean_negative_controls':4,
              'complete_false_recording_payloads':31,'current_owned_source_bindings':72,
              'local_positive_stack_limits':[8388608,-1],
              'source_bindings':{n:checker.sha(v) for n,v in sources.items()},
              'all_original_payload_files_included':True,
              'venv_is_tool_environment_excluded_from_wheel_evidence_manifest':True,
              'historical_development_evidence_retained_on_existing_public_branch':True,
              'public_download_validation_pending':True,'main_promotion_claim':False,
              'fresh_Lean_checks_during_packaging':0,'source_bound_proofs_added':0,
              'new_registered_source_certificates':0,'model_calls':0,'GPU_trials':0,
              'original_paper_fully_reproduced':False}
    checker.write(OUT/'results.json', report)
    checker.manifest(OUT)
    print(json.dumps({'status':report['status'],'archives':len(archives),
                      'compressed_bytes':sum(r['archive_bytes'] for r in archives.values()),
                      'files':sum(r['files'] for r in archives.values())}),flush=True)


if __name__=='__main__': main()
