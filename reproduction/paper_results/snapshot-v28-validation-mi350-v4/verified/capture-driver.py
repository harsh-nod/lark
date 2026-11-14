"""Capture the completed original 108-check run without repeating it."""
import hashlib
import json
from pathlib import Path
import shutil
import tarfile

BASE=Path('/tmp/lark-paper-v28-controls-mi350-v4-20261114')
OUT=Path('/tmp/lark-paper-v28-mi350-success-capture-v4-20261114')


def sha(path):
    d=hashlib.sha256()
    with path.open('rb') as source:
        for data in iter(lambda:source.read(1024*1024),b''):d.update(data)
    return d.hexdigest()


def write(path,value):path.write_text(json.dumps(value,indent=2)+'\n')


def main():
    assert not OUT.exists()
    assert not Path('/proc/2442871').exists() and not Path('/proc/2442872').exists()
    result=json.loads((BASE/'observer/results.json').read_text())
    assert result['status']=='complete-control-suite-passed' and result['exit_code']==0 and result['timed_out'] is False
    assert result['seconds']<=300 and result['completed_logs']==108
    assert result['source_checkpoint']=='f551fe0c1403de669ea2d98184c1ef48f46221c3'
    assert result['limits']=={'aggregate_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2}
    controls=json.loads((BASE/'validation/results.json').read_text())
    old=json.loads((BASE/'previous-v27-controls.json').read_text())
    names={r['name'] for r in old['checks']}
    assert len(names)==98 and [r for r in controls['checks'] if r['name'] in names]==old['checks']
    assert len(controls['checks'])==108 and controls['positive_replays']==10 and controls['negative_controls']==98
    assert len(list((BASE/'validation').glob('*.log')))==108
    assert controls['all_control_payloads_complete_during_replay'] is True
    bindings=json.loads((BASE/'bundle-manifest.json').read_text())
    assert len(bindings)==28 and all(sha(BASE/n)==h for n,h in bindings.items())
    OUT.mkdir();receipt=OUT/'receipt';receipt.mkdir()
    shutil.copyfile(__file__,receipt/'capture-driver.py')
    for relative in ['observer','validation']:shutil.copytree(BASE/relative,receipt/relative)
    for name in ['bundle-manifest.json','expected.json','launch.json','observer.py','launch.stdout','launch.stderr','previous-v27-controls.json']:
        shutil.copyfile(BASE/name,receipt/name)
    (receipt/'input-readers').mkdir()
    for name in ['replay_snapshot.py','check_snapshot_controls.py','snapshot_archives.py','snapshot_control_archives.py']:
        shutil.copyfile(BASE/'source/reproduction/paper_results'/name,receipt/'input-readers'/name)
    write(receipt/'results.json',{'status':'original-v28-full108-pass-captured-with-all-old-records',
        'original_process_result':result,'all108_control_logs_retained':True,
        'all98_previous_check_records_identical_and_ordered':True,'all28_actual_inputs_rehashed_after_run':True,
        'full_original_input_root_retained':str(BASE),'original_parent_and_child_absent':True,
        'experiment_restarts':0,'CI_or_publication_claim':False,
        'fresh_Lean_checks':0,'GPU_trials':0,'model_calls':0,'original_paper_fully_reproduced':False})
    write(receipt/'manifest.json',{p.relative_to(receipt).as_posix():sha(p) for p in receipt.rglob('*') if p.is_file()})
    assert all(p.stat().st_size<=10_000_000 for p in receipt.rglob('*') if p.is_file())
    archive=OUT/'receipt.tar.gz'
    with tarfile.open(archive,'w:gz') as tar:
        for p in sorted(receipt.rglob('*')):
            if p.is_file():tar.add(p,arcname=p.relative_to(receipt).as_posix(),recursive=False)
    answer={'status':'complete-original-success-receipt-captured','archive':str(archive),
            'archive_bytes':archive.stat().st_size,'archive_sha256':sha(archive),
            'files':sum(p.is_file() for p in receipt.rglob('*'))}
    write(OUT/'capture.json',answer);print(json.dumps(answer),flush=True)


if __name__=='__main__':main()
