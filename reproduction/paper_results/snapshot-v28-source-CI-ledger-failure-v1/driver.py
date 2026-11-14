"""Capture the original terminal ledger job; do not rerun its workload."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

OUT = Path('/tmp/lark-paper-v28-ledger-CI-job-v1-20261114')
ROOT = Path('/tmp/lark-paper-v27-20261113')
HEAD = '24288a0460f811f3e0ca5e8b28b64a3a4489503c'
JOB, RUN = 132463737398, 43600411242


def main():
    assert not OUT.exists(), 'Inspect the original capture before another invocation'
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    env = dict(os.environ, HTTPS_PROXY='socks5://127.0.0.1:19089')
    for name, suffix in [('job.json', ''), ('logs.raw', '/logs')]:
        response = subprocess.run(
            ['gh', 'api', f'repos/harsh-nod/lark/actions/jobs/{JOB}' + suffix],
            env=env, capture_output=True, timeout=90,
        )
        (OUT / name).write_bytes(response.stdout)
        (OUT / (name + '.stderr')).write_bytes(response.stderr)
        assert response.returncode == 0, response.stderr
    job = json.loads((OUT / 'job.json').read_text())
    assert job['id'] == JOB and job['run_id'] == RUN and job['head_sha'] == HEAD
    assert job['name'] == 'paper-ledger' and job['status'] == 'completed'
    source = subprocess.check_output(['git', 'show', HEAD + ':.github/workflows/ci.yml'], cwd=ROOT)
    (OUT / 'actual-source-ci.yml').write_bytes(source)
    assert b"record['positive_replays'] == 9 and record['negative_controls'] == 89" in source
    assert b"len(record['checks']) == len({row['name'] for row in record['checks']}) == 98" in source
    previous = ROOT / 'reproduction/paper_results/snapshot-v28-validation-mi350-v3/verified/validation'
    expected_names = {p.name for p in previous.glob('*.log')}
    assert len(expected_names) == 108
    logs = {}
    resources = []
    raw = (OUT / 'logs.raw').read_text()
    for line in raw.splitlines():
        start = line.find('{"control_log":')
        if start >= 0:
            record = json.loads(line[start:])
            name = record['control_log']
            assert Path(name).name == name and name.endswith('.log') and name not in logs
            logs[name] = record['text']
        if any(label in line for label in (
            'Elapsed (wall clock) time', 'Maximum resident set size', 'Exit status:',
            'User time (seconds)', 'System time (seconds)', 'temporary_directory',
            'RAM_filesystem_free_bytes', 'Command exited with non-zero status',
        )):
            resources.append(line)
    assert set(logs) <= expected_names
    target = OUT / 'dumped-control-logs'
    target.mkdir()
    for name, value in logs.items():
        (target / name).write_text(value)
    (OUT / 'actual-resource-observations.json').write_text(json.dumps(resources, indent=2) + '\n')
    exit_statuses = [int(value) for value in re.findall(r'Exit status:\s*(\d+)', raw)]
    result = {
        'status': 'original-terminal-ledger-job-captured', 'source_commit': HEAD,
        'run_id': RUN, 'job_id': JOB, 'job_conclusion': job['conclusion'],
        'actual_control_logs': len(logs),
        'all108_log_names_match_recorded_MI350_pass': set(logs) == expected_names,
        'actual_timed_process_exit_statuses': exit_statuses,
        'actual_source_final_assertions_use_old9positive89negative98total88copies': True,
        'assertion_error_present_in_raw_log': 'AssertionError' in raw,
        'ledger_job_passed': job['conclusion'] == 'success',
        'whole_workflow_success_claim': False,
        'limits_unchanged': {'aggregate_seconds': 300, 'per_replay_seconds': 120,
                             'max_independent_replayers': 2},
        'fresh_Lean_GPU_model_trials': 0, 'CI_reruns': 0,
        'original_paper_fully_reproduced': False,
    }
    (OUT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    (OUT / 'manifest.json').write_text(json.dumps({
        p.relative_to(OUT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(OUT.rglob('*')) if p.is_file()
    }, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
