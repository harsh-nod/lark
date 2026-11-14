"""Download a published snapshot anonymously and replay its controls outside Git."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def published_paths(root, commit, snapshot):
    """Use the pinned Git tree, including every physical part and helper."""
    relative = Path('reproduction/paper_results')

    def blob(name):
        return subprocess.check_output(['git', 'show', commit + ':' + name.as_posix()], cwd=root)

    provenance = json.loads(blob(snapshot / 'provenance.json'))
    schema = provenance['schema']
    assert type(schema) is int and schema in (1, 2), 'Unsupported published storage schema'
    names = subprocess.check_output(
        ['git', 'ls-tree', '-rz', '--name-only', commit, '--', snapshot.as_posix()], cwd=root,
    ).decode().split('\0')
    files = {Path(name) for name in names if name}
    manifest = json.loads(blob(snapshot / 'manifest.json'))
    assert files == {snapshot / name for name in manifest} | {snapshot / 'manifest.json'}, \
        'Complete committed snapshot inventory required'
    helpers = [relative / 'replay_snapshot.py', relative / 'check_snapshot_controls.py']
    if schema == 2:
        helpers += [relative / 'snapshot_archives.py', relative / 'snapshot_control_archives.py']
    return helpers + sorted(files)


def expected_counts(targets):
    negatives = (4 + 2*('production_cases' in targets) + 2*('production_proof_checks' in targets)
                 + 16*('numerical_studies' in targets) + 17*('full_shape_models' in targets)
                 + 8*sum(key in targets for key in ('ptx_pointwise_proof', 'ptx_dot_proof',
                         'ptx_matrix_proof', 'ptx_batched_proof', 'ptx_linear_proof')))
    positives = ((2 if 'numerical_studies' in targets else 1) + ('full_shape_models' in targets)
                 + sum(key in targets for key in ('ptx_pointwise_proof', 'ptx_dot_proof',
                       'ptx_matrix_proof', 'ptx_batched_proof', 'ptx_linear_proof')))
    return positives, negatives


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--snapshot', default='20261113-v26')
    parser.add_argument('--source-archive', required=True, type=Path)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--proxy', required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    assert not any((p/'.git').exists() for p in (out, *out.parents))
    assert len(args.commit) == 40 and all(c in '0123456789abcdef' for c in args.commit)
    assert Path(args.snapshot).name == args.snapshot and args.snapshot not in ('', '.', '..')
    out.mkdir(parents=True, exist_ok=False)
    downloaded = out/'download'
    relative = Path('reproduction/paper_results')
    snapshot = relative/'snapshots'/args.snapshot
    paths = published_paths(ROOT, args.commit, snapshot)
    records = []
    for name in paths:
        expected = subprocess.check_output(['git','show',args.commit+':'+str(name)],cwd=ROOT)
        destination = downloaded/name
        destination.parent.mkdir(parents=True, exist_ok=True)
        url = 'https://raw.githubusercontent.com/harsh-nod/lark/'+args.commit+'/'+name.as_posix()
        run = subprocess.run([
            'curl','--disable','--silent','--show-error','--fail','--location','--proto','=https',
            '--proto-redir','=https','--proxy',args.proxy,'--noproxy','',
            '--output',str(destination),'--write-out','%{http_code} %{ssl_verify_result}',url,
        ],capture_output=True,text=True,timeout=120)
        assert run.returncode == 0 and run.stdout == '200 0', str(name)+'\n'+run.stderr
        assert destination.read_bytes() == expected, 'Public bytes differ: '+str(name)
        records.append({'path':name.as_posix(),'bytes':len(expected),'sha256':sha(destination),'http_status':200,
                        'tls_verification':True,'curl_ssl_verify_result':0,'authorization_header':False})
    env = dict(os.environ, PATH='/nonexistent', PYTHONNOUSERSITE='1')
    env.pop('PYTHONPATH', None)
    env.pop('LEAN_PATH', None)
    result = subprocess.run([
        sys.executable,str(downloaded/relative/'check_snapshot_controls.py'),
        '--snapshot',str(downloaded/snapshot),'--source-archive',str(args.source_archive.resolve()),
        '--output',str(out/'validation'),
    ],cwd=downloaded,env=env,capture_output=True,text=True,timeout=300)
    (out/'public-replay.log').write_text(result.stdout+result.stderr)
    assert result.returncode == 0, result.stdout+result.stderr
    validation = json.loads((out/'validation/results.json').read_text())
    targets = json.loads((downloaded/snapshot/'targets.json').read_text())
    expected_positives, expected_controls = expected_counts(targets)
    assert validation['positive_replays'] == expected_positives and validation['negative_controls'] == expected_controls
    assert validation['replayer_sha256'] == sha(downloaded/relative/'replay_snapshot.py')
    assert validation['control_runner_sha256'] == sha(downloaded/relative/'check_snapshot_controls.py')
    report = {
        'schema':1,'recorded_at_utc':datetime.now(timezone.utc).isoformat(),
        'status':'anonymous-public-snapshot-download-and-no-git-replay-passed',
        'source_commit':args.commit,'snapshot':args.snapshot,'downloaded_files':records,
        'total_downloaded_bytes':sum(r['bytes'] for r in records),
        'authenticated_download_requests':False,'tls_verification':True,
        'all_downloads_match_committed_bytes':True,'git_on_replay_path':False,
        'outside_original_checkout':True,'positive_replays':expected_positives,'negative_controls':expected_controls,
        'fresh_lean_checks':0,'fresh_gpu_trials':0,'model_calls':0,
        'original_paper_fully_reproduced':False,'validation':validation,
        'checker_sha256':sha(Path(__file__)),
    }
    (out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    shutil.copyfile(Path(__file__),out/'checker.py')
    (out/'manifest.json').write_text(json.dumps({
        p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file()
    },indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','source_commit','total_downloaded_bytes','negative_controls')}))


if __name__ == '__main__':
    main()
