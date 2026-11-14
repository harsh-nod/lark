"""Finish v26 only after its original current CI and terminal public check pass."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time
import traceback

ROOT = Path('/tmp/lark-paper-v26-20261113')
OUT = Path('/tmp/lark-paper-v26-publication-finisher-v2-20261113')
CI = Path('/tmp/lark-paper-v26-source-ci-v2-20261113')
SOURCE = 'ce5611655946a0a8cca76f97beb8f85bf8f4fc2b'
OLD = 'db1eb9bbb96d365987f685e085ff3e4a314ec128'
BRANCH = 'refs/heads/reproduction/paper-v26'
PACKAGER = Path('/tmp/lark-package-paper-v26-publication-v2-20261113.py')
PROMOTER = Path('/tmp/lark-promote-paper-v26-v2-20261113.py')
PREFIXES = ['reproduction/paper_results/' + name for name in
            ['snapshot-v26-publication', 'snapshot-v26-source-ci-v2', 'snapshot-v26-source-ci-failed-v1']]
DOCS = ['README.md', 'reproduction/paper_results/README.md', 'reproduction/paper_results/ARCHIVE_FORMAT.md']


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(name, value):
    path = OUT / name
    temporary = path.with_name(path.name + '.next')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def stage(name, **value):
    write('progress.json', {'pid': os.getpid(), 'stage': name,
                           'at_utc': datetime.now(timezone.utc).isoformat(), **value})


def call(name, command, timeout=180):
    stage(name, command=command)
    with (OUT / (name + '.stdout')).open('w') as stdout, (OUT / (name + '.stderr')).open('w') as stderr:
        child = subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr)
        stage(name, child_pid=child.pid, command=command)
        try:
            code = child.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            stage(name + '-original-child-observation-expired', child_pid=child.pid, command=command)
            raise RuntimeError('Inspect the original live child and external state; do not restart this action')
    write(name + '.json', {'exit_code': code, 'command': command})
    if code:
        raise RuntimeError(name + ' failed; inspect retained logs/state before any next action')
    return (OUT / (name + '.stdout')).read_text().strip()


def git(*args):
    return subprocess.check_output(['git', *args], cwd=ROOT, text=True).strip()


def main():
    assert not OUT.exists(), 'Inspect original finisher state/PID rather than launching again'
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    os.environ['HTTPS_PROXY'] = 'socks5://127.0.0.1:19089'
    bindings = {'source_commit': SOURCE, 'old_main': OLD, 'run_id': 43544667567,
                'CI_observer_pid': 4194259, 'packager_sha256': sha(PACKAGER),
                'promoter_sha256': sha(PROMOTER), 'model_calls': 0, 'gpu_trials': 0,
                'CI_reruns': 0, 'original_paper_fully_reproduced': False}
    write('bindings.json', bindings)
    public = json.loads(Path('/tmp/lark-paper-v26-publication-return-v2-20261113/verified/observer/results.json').read_text())
    assert public['source_commit'] == SOURCE and public['exit_code'] == 0 and not public['timed_out']
    assert public['downloaded_files'] == 17 and public['downloaded_bytes'] == 238899106
    for poll in range(121):
        if (CI / 'results.json').exists():
            break
        if poll == 120:
            stage('bounded-current-CI-observation-ended-without-mutations', poll=poll)
            return
        try:
            os.kill(4194259, 0)
        except ProcessLookupError:
            stage('original-CI-observer-missing-inspect-actual-run-without-mutations', poll=poll)
            return
        stage('waiting-original-current-CI-observer-no-mutations', poll=poll)
        time.sleep(30)
    ci = json.loads((CI / 'results.json').read_text())
    assert ci['source_commit'] == SOURCE and ci['run_id'] == 43544667567
    assert ci['status'] == 'exact-source-CI-all-23-passed' and ci['successful_jobs'] == 23
    assert len(set(ci['expected_jobs'])) == 23 and 'paper-ledger' in ci['expected_jobs']
    assert git('rev-parse', 'HEAD') == SOURCE and not git('status', '--porcelain')
    assert sha(PACKAGER) == bindings['packager_sha256'] and sha(PROMOTER) == bindings['promoter_sha256']
    call('package-actual-terminal-receipts', ['/usr/bin/python3', str(PACKAGER)])
    expected_dirty = set(DOCS)
    for prefix in PREFIXES:
        expected_dirty.update(p.relative_to(ROOT).as_posix() for p in (ROOT / prefix).rglob('*') if p.is_file())
    dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=all'],
                                    cwd=ROOT, text=True)
    assert {line[3:] for line in dirty.splitlines()} == expected_dirty
    call('whitespace-check', ['git', 'diff', '--check'])
    call('stage-receipts-and-docs', ['git', 'add', *DOCS, *PREFIXES])
    call('commit-receipts-and-docs', ['git', 'commit', '-m',
         'Record v26 anonymous replay and all twenty-three source CI jobs [skip ci]'])
    target = git('rev-parse', 'HEAD')
    assert not git('status', '--porcelain')
    write('candidate.json', {'source_commit': SOURCE, 'candidate': target,
          'source_CI_jobs': 23, 'candidate_CI_executed': False,
          'only_three_docs_and_new_receipts_after_source': True})
    branch = json.loads(call('read-current-public-branch', ['gh', 'api',
        'repos/harsh-nod/lark/git/ref/heads/reproduction/paper-v26']))
    main_ref = json.loads(call('read-current-public-main', ['gh', 'api',
        'repos/harsh-nod/lark/git/ref/heads/main']))
    assert branch['object']['sha'] == SOURCE and main_ref['object']['sha'] == OLD
    call('publish-receipts', ['git', '-c', 'http.proxy=socks5h://127.0.0.1:19089',
                            'push', '--porcelain', 'origin', target + ':' + BRANCH])
    assert sha(PROMOTER) == bindings['promoter_sha256']
    call('main-preflight', ['/usr/bin/python3', str(PROMOTER), '--target', target, '--check-only'])
    call('main-apply', ['/usr/bin/python3', str(PROMOTER), '--target', target])
    receipt = json.loads(Path('/tmp/lark-paper-v26-ci-main-v2-20261113/results.json').read_text())
    assert receipt['status'] == 'v26-main-fast-forward-complete' and receipt['promoted_commit'] == target
    write('results.json', {'status': 'v26-source-publication-CI23-and-main-complete',
          'source_commit': SOURCE, 'main': target, 'source_CI_jobs': 23,
          'public_download_files': 17, 'positive_replays': 8, 'negative_controls': 81,
          'earlier_source_CI_kept_failed': True, 'CI_reruns': 0,
          'model_calls': 0, 'gpu_trials': 0, 'original_paper_fully_reproduced': False,
          'main_receipt': '/tmp/lark-paper-v26-ci-main-v2-20261113/results.json'})
    print((OUT / 'results.json').read_text(), flush=True)


if __name__ == '__main__':
    try:
        main()
    except Exception:
        if OUT.exists():
            (OUT / 'exception.txt').write_text(traceback.format_exc())
        raise
