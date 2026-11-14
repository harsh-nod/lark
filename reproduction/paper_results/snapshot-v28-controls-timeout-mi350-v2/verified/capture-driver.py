"""Retain the original timed-out suite, full failed-input inventory and profile."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile

BASE=Path('/tmp/lark-paper-v28-controls-mi350-v2-20261114')
PROFILE=Path('/tmp/lark-paper-v28-positive-profile-mi350-v1-20261114')
OUT=Path('/tmp/lark-paper-v28-mi350-failure-capture-v2-20261114')


def sha(path):
    d=hashlib.sha256()
    with path.open('rb') as source:
        for data in iter(lambda:source.read(1024*1024),b''):d.update(data)
    return d.hexdigest()


def write(path,value):
    path.write_text(json.dumps(value,indent=2)+'\n')


def main():
    assert not OUT.exists()
    assert not Path('/proc/2239610').exists() and not Path('/proc/2239611').exists()
    original=json.loads((BASE/'observer/process-result.json').read_text())
    assert original['timed_out'] is True and original['completed_logs']==106
    assert original['limits']=={'aggregate_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2}
    OUT.mkdir()
    receipt=OUT/'receipt';receipt.mkdir()
    shutil.copyfile(__file__,receipt/'capture-driver.py')
    for relative in ['observer','validation']:
        shutil.copytree(BASE/relative,receipt/relative)
    for name in ['bundle-manifest.json','expected.json','launch.json','observer.py',
                 'launch.stdout','launch.stderr','previous-v27-controls.json']:
        shutil.copyfile(BASE/name,receipt/name)
    shutil.copytree(BASE/'source/reproduction/paper_results',receipt/'input-readers',
                    ignore=lambda directory,names:set(names)-{
                        'replay_snapshot.py','check_snapshot_controls.py','snapshot_archives.py','snapshot_control_archives.py'})
    # All incomplete control copies, materialized reader inputs and producer
    # parts remain on the host, with every actual file bound here. No deletion.
    temporary={p.relative_to(BASE).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
               for p in (BASE/'temporary').rglob('*') if p.is_file()}
    write(receipt/'retained-failed-workspaces.json',temporary)
    bindings=json.loads((BASE/'bundle-manifest.json').read_text())
    assert all(sha(BASE/n)==h for n,h in bindings.items())
    profile=json.loads((PROFILE/'results.json').read_text())
    assert profile['reader_success_cache_used'] is False and profile['full108_release_gate_satisfied'] is False
    (receipt/'diagnostic-profile').mkdir()
    for p in PROFILE.iterdir():
        if p.is_file():shutil.copyfile(p,receipt/'diagnostic-profile'/p.name)
    for suffix in ['stdout','stderr']:
        source=Path('/tmp/lark-paper-v28-positive-profile-v1-20261114.'+suffix)
        shutil.copyfile(source,receipt/'diagnostic-profile'/('process.'+suffix))
    write(receipt/'results.json',{'status':'original-v28-full108-timeout-and-fresh-positive-profile-retained',
        'original_process_result':original,'original_parent_and_child_absent':True,
        'all28_original_inputs_rehashed_and_still_retained':True,'full_original_input_root':str(BASE),
        'retained_failed_workspace_files':len(temporary),'retained_failed_workspace_bytes':sum(r['bytes'] for r in temporary.values()),
        'failed_workspace_inventory':'retained-failed-workspaces.json','failed_workspaces_deleted':False,
        'profile':profile,'experiment_restarts':0,'CI_reruns':0,
        'fresh_Lean_checks':0,'GPU_trials':0,'model_calls':0,'original_paper_fully_reproduced':False,
        'scope':'106 written logs do not establish the required full108 gate. Entire original bundle and failed workspaces remain on MI350. The archive contains all logs, source readers, metadata and a complete byte inventory of retained failed workspaces, not duplicate multi-gigabyte payloads.'})
    write(receipt/'manifest.json',{p.relative_to(receipt).as_posix():sha(p) for p in receipt.rglob('*') if p.is_file()})
    assert all(p.stat().st_size<=10_000_000 for p in receipt.rglob('*') if p.is_file())
    archive=OUT/'receipt.tar.gz'
    with tarfile.open(archive,'w:gz') as tar:
        for p in sorted(receipt.rglob('*')):
            if p.is_file():tar.add(p,arcname=p.relative_to(receipt).as_posix(),recursive=False)
    result={'status':'complete-original-failure-receipt-captured','archive':str(archive),
            'archive_bytes':archive.stat().st_size,'archive_sha256':sha(archive),
            'files':sum(p.is_file() for p in receipt.rglob('*'))}
    write(OUT/'capture.json',result);print(json.dumps(result),flush=True)


if __name__=='__main__':main()
