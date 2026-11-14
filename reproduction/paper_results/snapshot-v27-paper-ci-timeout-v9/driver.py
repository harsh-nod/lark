"""Read a completed CI failure and retain all logs without rerunning it."""
import hashlib
import json
import os
from pathlib import Path
import subprocess

OUT = Path('/tmp/lark-paper-v27-source-ci-ledger-failed-v9-20261114')
JOB = 132397468298
RUN = 43578339325
SOURCE = 'd03ef075945f447a63862b0adf4197d83caad279'


def main():
    OUT.mkdir(exist_ok=False)
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    env = dict(os.environ, HTTPS_PROXY='socks5://127.0.0.1:19089')
    for name, suffix in [('job.json', ''), ('logs.raw', '/logs')]:
        result = subprocess.run(['gh', 'api', f'repos/harsh-nod/lark/actions/jobs/{JOB}' + suffix],
                                env=env, capture_output=True, timeout=90)
        (OUT / name).write_bytes(result.stdout)
        (OUT / (name + '.stderr')).write_bytes(result.stderr)
        assert result.returncode == 0, result.stderr
    job = json.loads((OUT / 'job.json').read_text())
    assert job['id'] == JOB and job['run_id'] == RUN and job['head_sha'] == SOURCE
    assert job['status'] == 'completed' and job['conclusion'] == 'failure'
    logs = OUT / 'control-logs'
    logs.mkdir()
    raw = (OUT / 'logs.raw').read_text()
    for line in raw.splitlines():
        start = line.find('{"control_log":')
        if start < 0:
            continue
        row = json.loads(line[start:])
        name = row['control_log']
        assert Path(name).name == name and name.endswith('.log')
        assert not (logs / name).exists()
        (logs / name).write_text(row['text'])
    result = {
        'status': 'original-buffered-auditor-ledger-job-failed',
        'source_commit': SOURCE, 'run_id': RUN, 'job_id': JOB,
        'completed_logs': len(list(logs.glob('*.log'))),
        'failed_steps': [s['name'] for s in job['steps'] if s['conclusion'] == 'failure'],
        'diagnostics': [line for line in raw.splitlines() if any(key in line for key in
            ['User time (seconds):', 'System time (seconds):', 'Elapsed (wall clock)',
             'Maximum resident set size', 'Exit status:', '##[error]'])],
        'reruns': 0,
    }
    (OUT / 'analysis.json').write_text(json.dumps(result, indent=2) + '\n')
    (OUT / 'manifest.json').write_text(json.dumps({p.relative_to(OUT).as_posix():
        hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.rglob('*'))
        if p.is_file() and p.name != 'manifest.json'}, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
