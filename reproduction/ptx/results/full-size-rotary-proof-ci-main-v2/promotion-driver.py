"""Check exact RoPE source, publication and all24 CI jobs before a non-force main update."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import math
import os
from pathlib import Path
import re
import subprocess

ROOT = Path('/tmp/lark-ptx-rotary-refinement-20261113')
MAIN = Path('/home/harsh/lark')
OUT = Path('/tmp/lark-ptx-rotary-ci-main-v2-20261113')
SOURCE = '898d54045af3a60367650bb56afcf0b7b3615ba1'
OLD = '4a7616fa7a668fec2aad85c2989cf3b4b91e2764'
RUN = 43557902131
PROOF = 'reproduction/ptx/results/full-size-rotary-proof-v1'
PUBLICATION = 'reproduction/ptx/results/full-size-rotary-proof-publication-v3'
CI = 'reproduction/ptx/results/full-size-rotary-proof-ci-v2'
FAILED = 'reproduction/ptx/results/full-size-rotary-proof-publication-preflight-failed-v1'
TRANSPORT = 'reproduction/ptx/results/full-size-rotary-proof-transport-v1'
HISTORY_PREFIXES = ('reproduction/ptx/results/full-size-rotary-proof-publication-v2', 'reproduction/ptx/results/full-size-rotary-proof-ci-failed-v1', 'reproduction/ptx/results/full-size-rotary-proof-ci-ledger-failed-v1', 'reproduction/ptx/results/full-size-rotary-proof-ci-ledger-success-v2', 'reproduction/ptx/results/full-size-rotary-proof-io-local-timeout-v1', 'reproduction/ptx/results/full-size-rotary-proof-io-mi350-v1', 'reproduction/paper_results/original-artifact-rope-refresh-20261113-v1')
DOC_CHANGES = {
    'README.md': [(
        'installed-wheel replay passed locally. The complete evidence and failed\n'
        'development history are retained; anonymous publication verification and the\n'
        'new source CI job remain pending. This adds no original model or NVIDIA result.\n',
        'installed-wheel replay passed. The complete evidence and failed development\n'
        'history are retained. Anonymous publication verification and all twenty-four\n'
        'source CI jobs passed at `898d540`. This adds no original model or NVIDIA result.\n')],
    'reproduction/ptx/ROTARY.md': [(
        'Anonymous publication verification and the new source CI job remain pending.\n',
        'The [anonymous publication record](results/full-size-rotary-proof-publication-v3/results.json)\n'
        'verified all 81 changed files (244,981,348 bytes), 18 archives and 4,414 members\n'
        'against source `898d540`, with verified TLS and isolated Python outside Git.\n'
        'The [actual source CI record](results/full-size-rotary-proof-ci-v2/results.json)\n'
        'records all twenty-four jobs passing, including fresh RoPE export/replay and\n'
        'both control suites. Receipt commits change only documentation and recorded\n'
        'publication/CI metadata; SDK, Lean, tests, workflow and frozen snapshots retain\n'
        'their exact tested source identities. No CI claim is made for those metadata commits.\n')],
}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def call(command, cwd=ROOT):
    environment = dict(os.environ, HTTPS_PROXY='socks5://127.0.0.1:19089')
    return subprocess.check_output(command, cwd=cwd, env=environment, text=True, timeout=60).strip()


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def checked_folder(prefix):
    folder = ROOT / prefix
    require(folder.is_dir() and not any(p.is_symlink() for p in folder.rglob('*')), 'Missing or linked receipt')
    inventory = {p.relative_to(folder).as_posix(): sha(p) for p in folder.rglob('*') if p.is_file() and p != folder / 'manifest.json'}
    require(inventory == read(folder / 'manifest.json'),
            'Exact receipt inventory differs: ' + prefix)
    return {prefix + '/' + name for name in [*inventory, 'manifest.json']}


def expected_doc(name):
    data = call(['git', 'show', SOURCE + ':' + name]) + '\n'
    for before, after in DOC_CHANGES[name]:
        require(data.count(before) == 1, 'Original document anchor differs')
        data = data.replace(before, after)
    return data


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', required=True)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    target = args.target
    require(re.fullmatch('[0-9a-f]{40}', target) is not None, 'Concrete metadata candidate required')
    require(call(['git', 'rev-parse', 'HEAD']) == target and not call(['git', 'status', '--porcelain']),
            'Clean pinned candidate required')
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
            and call(['git', 'branch', '--show-current'], MAIN) == 'main'
            and not call(['git', 'status', '--porcelain'], MAIN), 'Clean local main changed')
    for ancestor in (OLD, SOURCE):
        subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, target], cwd=ROOT, check=True)
    expected = set(DOC_CHANGES)
    for prefix in (PUBLICATION, CI, FAILED, TRANSPORT, *HISTORY_PREFIXES):
        expected |= checked_folder(prefix)
    changed = call(['git', 'diff', '--name-only', SOURCE, target]).splitlines()
    require(set(changed) == expected, 'Only exact receipts and two documents may follow tested source')
    require(all((ROOT / name).read_text() == expected_doc(name) for name in DOC_CHANGES),
            'Exact documentation updates required')
    checked_folder(PROOF)
    require(sha(ROOT / PROOF / 'manifest.json') == '4a421b83c407d0f1807e1cdab2ba0000cb63a2de08db77c4e297e5a6f85d503d',
            'Frozen complete RoPE packet changed')
    require(sha(ROOT / 'reproduction/paper_results/snapshots/20261113-v26/manifest.json')
            == '251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed', 'Frozen v26 changed')
    publication = read(ROOT / PUBLICATION / 'results.json')
    binding = read(ROOT / PUBLICATION / 'binding.json')
    require(publication['status'] == 'anonymous-exact-source-RoPE-publication-verified'
            and publication['source_commit'] == binding['source_commit'] == SOURCE
            and publication['recorded_reader_exit_code'] == 0
            and publication['all_TLS_verified'] is publication['standalone_reader_outside_Git'] is True
            and publication['authorization_headers_used'] is False
            and publication['binding_sha256'] == sha(ROOT / PUBLICATION / 'binding.json')
            and publication['verifier_sha256'] == sha(ROOT / PUBLICATION / 'verifier.py')
            and publication['archives_checked'] == 18 and publication['archive_members_checked'] == 4414,
            'Actual anonymous source observation differs')
    records = binding['files']
    public_paths = set(call(['git', 'diff', '--name-only', OLD, SOURCE]).splitlines())
    require(len(records) == len(public_paths) == publication['files_checked'] == 81
            and {r['path'] for r in records} == public_paths
            and sum(r['bytes'] for r in records) == publication['bytes_checked'] == 244981348,
            'Every anonymous changed file required')
    for row in records:
        data = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=ROOT, timeout=60)
        require(row['http_status'] == 200 and row['tls_verification'] is row['matches_committed_bytes'] is True
                and row['authorization_header'] is False and len(data) == row['bytes']
                and hashlib.sha256(data).hexdigest() == row['sha256'], 'Exact public Git bytes differ')
    prior = read(ROOT / HISTORY_PREFIXES[1] / 'results.json')
    require(prior['status'] == 'exact-source-CI-terminal-non-success'
            and prior['source_commit'] == '9ffe009f5ff3a7635d6b3708efa1bf73a840b0c9'
            and prior['run_id'] == 43555447049 and prior['successful_jobs'] == 23,
            'Earlier actual failed CI must remain retained')
    local = read(ROOT / HISTORY_PREFIXES[4] / 'results.json')
    require(local['status'] == 'ledger-validation-failed' and local['exit_code'] == 124
            and local['aggregate_cap_seconds'] == 300 and local['source_commit'] == SOURCE,
            'Earlier local timeout must remain unaccepted')
    mi = read(ROOT / HISTORY_PREFIXES[5] / 'results.json')
    require(mi['status'] == 'complete-control-suite-passed'
            and mi['source_checkpoint'] == SOURCE and mi['timed_out'] is False
            and all(type(mi[k]) is int and mi[k] == value for k, value in
                    {'exit_code': 0, 'positive_replays': 8, 'negative_controls': 81}.items())
            and mi['all_89_checks_completed'] is True
            and type(mi['seconds']) in (int, float) and math.isfinite(mi['seconds'])
            and 0 <= mi['seconds'] < 300
            and mi['limits'] == {'aggregate_seconds': 300, 'per_replay_seconds': 120,
                                 'max_independent_replayers': 2}, 'Actual MI350 all89 validation required')
    ledger = read(ROOT / HISTORY_PREFIXES[3] / 'results.json')
    require(ledger['status'] == 'exact-source-ledger-job-success-with-all89-logs-retained'
            and ledger['source_commit'] == SOURCE and ledger['run_id'] == RUN
            and ledger['retained_control_logs'] == 89 and ledger['aggregate_cap_seconds'] == 300,
            'Actual unchanged-limit CI ledger success required')
    names = set(re.findall(r'^  ([a-z][a-z0-9-]*):$',
                (ROOT / '.github/workflows/ci.yml').read_text().split('\njobs:\n', 1)[1], re.M))
    receipt = read(ROOT / CI / 'results.json')
    require(len(names) == 24 and receipt['status'] == 'exact-source-CI-all-24-passed'
            and receipt['source_commit'] == SOURCE and receipt['run_id'] == RUN
            and receipt['successful_jobs'] == 24 and set(receipt['expected_jobs']) == names,
            'Actual24 source CI record differs')
    ci = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}']))
    jobs = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}/jobs?per_page=100']))
    require(ci['head_sha'] == SOURCE and ci['status'] == 'completed' and ci['conclusion'] == 'success'
            and ci['head_branch'] == 'reproduction/ptx-rotary-refinement' and ci['run_attempt'] == 1
            and ci['event'] == 'push' and ci['name'] == 'Verify'
            and jobs['total_count'] == len(jobs['jobs']) == 24
            and {j['name'] for j in jobs['jobs']} == names
            and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs']),
            'Fresh actual24 source CI successes required')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
            'Remote main changed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/ptx-rotary-refinement']))
            ['object']['sha'] == target, 'Published metadata candidate differs')
    if args.check_only:
        print(json.dumps({'status': 'RoPE-main-preflight-passed', 'source_ci_jobs': 24,
                          'receipt_docs_delta_files': len(changed), 'anonymous_files': 81}))
        return
    require(not OUT.exists(), 'Inspect original promotion state instead of repeating an update')
    OUT.mkdir()
    (OUT / 'promotion-driver.py').write_bytes(Path(__file__).read_bytes())
    state = {'schema': 1, 'status': 'RoPE-main-all-gates-passed-update-pending',
             'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
             'source_CI_executed_for_promoted_commit': False, 'old_main': OLD, 'promoted_commit': target,
             'source_ci': ci, 'source_ci_jobs': jobs, 'changed_paths_after_checked_source': changed,
             'helper_sha256': sha(Path(__file__)), 'model_calls_by_promotion': 0,
             'fresh_Lean_checks_by_promotion': 0, 'gpu_trials_by_promotion': 0,
             'force': False, 'original_paper_fully_reproduced': False}
    write(OUT / 'progress.json', state)
    write(OUT / 'update.json', {'sha': target, 'force': False})
    state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    require(state['remote_update']['object']['sha'] == target, 'Remote main result differs')
    state['status'] = 'RoPE-remote-main-fast-forwarded-local-pending'
    write(OUT / 'progress.json', state)
    state['local_merge'] = call(['git', 'merge', '--ff-only', target], MAIN)
    subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', target, OLD], cwd=ROOT, check=True)
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == target and not call(['git', 'status', '--porcelain'], MAIN),
            'Local main did not reach the clean exact candidate')
    state['status'] = 'RoPE-public-main-nonforce-fast-forward-verified'
    state['finished_at_utc'] = datetime.now(timezone.utc).isoformat()
    write(OUT / 'results.json', state)
    write(OUT / 'progress.json', state)
    write(OUT / 'manifest.json', {p.name: sha(p) for p in sorted(OUT.iterdir()) if p.is_file()})
    print(json.dumps({'status': state['status'], 'main': target, 'source_CI': SOURCE, 'source_jobs': 24}))


if __name__ == '__main__':
    main()
