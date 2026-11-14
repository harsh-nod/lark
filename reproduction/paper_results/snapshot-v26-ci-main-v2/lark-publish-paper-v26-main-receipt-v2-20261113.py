"""Publish the actual completed v26 main promotion as guarded receipt-only metadata."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import traceback

ROOT = Path('/tmp/lark-paper-v26-20261113')
MAIN = Path('/home/harsh/lark')
OUT = Path('/tmp/lark-paper-v26-main-receipt-publication-v2-20261113')
PROMOTION = Path('/tmp/lark-paper-v26-ci-main-v2-20261113')
FINISHER = Path('/tmp/lark-paper-v26-publication-finisher-v2-20261113')
OLD = 'c6c02ac67657dc8089368b210300d2296d122762'
SOURCE = 'ce5611655946a0a8cca76f97beb8f85bf8f4fc2b'
PREFIX = 'reproduction/paper_results/snapshot-v26-ci-main-v2'
DOC = 'reproduction/paper_results/README.md'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    temporary = path.with_name(path.name + '.next')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def call(name, command, cwd=ROOT):
    write(OUT / 'progress.json', {'pid': os.getpid(), 'stage': name, 'command': command,
                               'at_utc': datetime.now(timezone.utc).isoformat()})
    with (OUT / (name + '.stdout')).open('w') as stdout, (OUT / (name + '.stderr')).open('w') as stderr:
        child = subprocess.Popen(command, cwd=cwd, stdout=stdout, stderr=stderr)
        write(OUT / 'progress.json', {'pid': os.getpid(), 'child_pid': child.pid, 'stage': name, 'command': command})
        try:
            code = child.wait(timeout=180)
        except subprocess.TimeoutExpired:
            raise RuntimeError('Inspect original child/PID and external state; do not repeat the mutation')
    write(OUT / (name + '.json'), {'exit_code': code, 'command': command})
    assert code == 0, name
    return (OUT / (name + '.stdout')).read_text().strip()


def git(*args, root=ROOT):
    return subprocess.check_output(['git', *args], cwd=root, text=True).strip()


def manifest(folder):
    write(folder / 'manifest.json', {p.name: sha(p) for p in sorted(folder.iterdir()) if p.is_file()})


def main():
    assert not OUT.exists(), 'Inspect existing publication/PID instead of relaunching'
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    os.environ['HTTPS_PROXY'] = 'socks5://127.0.0.1:19089'
    for root in [ROOT, MAIN]:
        assert git('rev-parse', 'HEAD', root=root) == OLD and not git('status', '--porcelain', root=root)
    promotion = json.loads((PROMOTION / 'results.json').read_text())
    completed = json.loads((FINISHER / 'results.json').read_text())
    assert promotion['status'] == 'v26-main-fast-forward-complete' and promotion['promoted_commit'] == OLD
    assert promotion['source_checkpoint'] == SOURCE and promotion['source_CI_executed_for_promoted_commit'] is False
    assert all(promotion['checks'].values())
    assert completed['status'] == 'v26-source-publication-CI23-and-main-complete' and completed['main'] == OLD
    assert completed['source_CI_jobs'] == 23
    run = json.loads(call('fresh-successful-source-run', ['gh', 'api',
        'repos/harsh-nod/lark/actions/runs/43544667567']))
    assert run['head_sha'] == SOURCE and run['status'] == 'completed' and run['conclusion'] == 'success'
    assert run['run_attempt'] == 1
    jobs = json.loads(call('fresh-successful-source-jobs', ['gh', 'api',
        'repos/harsh-nod/lark/actions/runs/43544667567/jobs?per_page=100']))
    assert jobs['total_count'] == len(jobs['jobs']) == 23
    assert all(j['status'] == 'completed' and j['conclusion'] == 'success' and j['run_id'] == 43544667567 for j in jobs['jobs'])
    for label, resource in [('main', 'main'), ('branch', 'reproduction/paper-v26')]:
        assert json.loads(call('read-before-' + label, ['gh', 'api',
            'repos/harsh-nod/lark/git/ref/heads/' + resource]))['object']['sha'] == OLD
    destination = ROOT / PREFIX
    assert not destination.exists()
    shutil.copytree(PROMOTION, destination)
    shutil.copytree(FINISHER, destination / 'finisher')
    manifest(destination / 'finisher')
    for path in ['/tmp/lark-promote-paper-v26-v2-20261113.py',
                 '/tmp/lark-package-paper-v26-publication-v2-20261113.py', str(Path(__file__))]:
        shutil.copyfile(path, destination / Path(path).name)
    write(destination / 'receipt-scope.json', {'status': 'actual-completed-main-promotion-receipt',
          'source_commit': SOURCE, 'source_CI_run': 43544667567, 'source_CI_jobs': 23,
          'actual_first_main_promotion': OLD, 'CI_executed_for_receipt_only_commit': False,
          'model_calls': 0, 'GPU_trials': 0, 'Lean_checks_by_receipt_publication': 0,
          'original_paper_fully_reproduced': False})
    manifest(destination)
    readme = ROOT / DOC
    anchor = 'The earlier v25 snapshot freezes **3,623 evidence files**'
    value = readme.read_text()
    assert value.count(anchor) == 1
    readme.write_text(value.replace(anchor,
        'The [completed main-promotion record](snapshot-v26-ci-main-v2/results.json)\n'
        'records the guarded fast-forward from `db1eb9b` to `c6c02ac`. All 23 source\n'
        'CI jobs passed at `ce56116`; the promoted commit changes only the three\n'
        'documentation files and publication/CI receipts after that source.\n'
        'This later promotion receipt also adds no executable or snapshot changes\n'
        'and claims no separate CI run for its metadata-only commit.\n\n' + anchor))
    expected = {DOC} | {p.relative_to(ROOT).as_posix() for p in destination.rglob('*') if p.is_file()}
    dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'], cwd=ROOT, text=True)
    assert {line[3:] for line in dirty.splitlines()} == expected
    call('whitespace-check', ['git', 'diff', '--check'])
    call('stage-receipt', ['git', 'add', DOC, PREFIX])
    call('commit-receipt', ['git', 'commit', '-m', 'Retain actual v26 main promotion and source CI bindings [skip ci]'])
    target = git('rev-parse', 'HEAD')
    assert set(git('diff', '--name-only', OLD, target).splitlines()) == expected
    assert not git('status', '--porcelain')
    assert not git('diff', '--name-only', SOURCE, target, '--', 'lark_kernels', 'lean', 'lean-real',
                   'tests', '.github', 'pyproject.toml', 'reproduction/paper_results/snapshots')
    call('publish-branch', ['git', '-c', 'http.proxy=socks5h://127.0.0.1:19089', 'push', '--porcelain',
                          'origin', target + ':refs/heads/reproduction/paper-v26'])
    assert json.loads(call('fresh-public-branch', ['gh', 'api',
        'repos/harsh-nod/lark/git/ref/heads/reproduction/paper-v26']))['object']['sha'] == target
    assert json.loads(call('fresh-main-before-update', ['gh', 'api',
        'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD
    write(OUT / 'update.json', {'sha': target, 'force': False})
    response = json.loads(call('nonforce-main-update', ['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    assert response['object']['sha'] == target
    call('local-main-fast-forward', ['git', 'merge', '--ff-only', target], cwd=MAIN)
    call('tracking-main-CAS', ['git', 'update-ref', 'refs/remotes/origin/main', target, OLD])
    assert git('rev-parse', 'HEAD', root=MAIN) == target and not git('status', '--porcelain', root=MAIN)
    assert json.loads(call('fresh-main-after-update', ['gh', 'api',
        'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == target
    write(OUT / 'results.json', {'status': 'v26-main-promotion-receipt-published', 'main': target,
          'previous_main': OLD, 'source_commit': SOURCE, 'source_CI_jobs': 23,
          'only_receipt_and_paper_README_added': True, 'new_CI_for_metadata_commit': False,
          'new_model_GPU_Lean_or_snapshot_replays': 0, 'original_paper_fully_reproduced': False})
    print((OUT / 'results.json').read_text(), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception:
        if OUT.exists():
            (OUT / 'exception.txt').write_text(traceback.format_exc())
        raise
