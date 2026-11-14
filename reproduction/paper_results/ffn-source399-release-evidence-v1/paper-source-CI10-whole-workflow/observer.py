"""Observe one already-running source CI; never rerun jobs or experiments."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

OUT = Path('/tmp/lark-paper-v27-source-ci-v10-20261114')
COMMIT = sys.argv[2]
assert len(COMMIT) == 40 and all(c in '0123456789abcdef' for c in COMMIT)
RUN = int(sys.argv[1])
EXPECTED = {
    'paper-ledger', 'reference-identity', 'native-awq-components', 'native-sglang-real',
    'native-sglang-rmsnorm', 'exact-real', 'native-rope',
    'qknorm-rope-split-real', 'native-awq-real', 'native-flashinfer-real',
    'softmax-grid', 'native-flashinfer-rmsnorm', 'native-qknorm-rope',
    'proof-tests', 'qknorm-rope-real', 'softmax-block', 'softmax-race',
    'fused-real', 'softmax-source', 'softmax-real', 'ptx-matrix', 'ptx-batched', 'ptx-linear', 'ptx-rotary',
}


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    assert not OUT.exists(), 'Inspect the original observer/process before another launch'
    OUT.mkdir()
    (OUT / 'observer.py').write_bytes(Path(__file__).read_bytes())
    started = time.monotonic()
    history = []
    environment = os.environ.copy()
    environment['HTTPS_PROXY'] = 'socks5://127.0.0.1:19089'
    for poll in range(1, 81):
        values = []
        try:
            for resource in [f'actions/runs/{RUN}', f'actions/runs/{RUN}/jobs?per_page=100']:
                proc = subprocess.run(['gh', 'api', 'repos/harsh-nod/lark/' + resource],
                                      env=environment, capture_output=True, text=True, timeout=40)
                if proc.returncode:
                    raise RuntimeError(proc.stderr[:2000])
                values.append(json.loads(proc.stdout))
            run, response = values
            assert run['id'] == RUN and run['head_sha'] == COMMIT
            assert run['head_branch'] == 'reproduction/paper-v27'
            assert run['event'] == 'push' and run['name'] == 'Verify' and run['run_attempt'] == 1
            jobs = response['jobs']
            assert response['total_count'] == len(jobs) == 24
            assert len({j['id'] for j in jobs}) == 24
            assert {j['name'] for j in jobs} == EXPECTED
            write(OUT / 'run.json', run)
            write(OUT / 'jobs.json', response)
            observation = {'poll': poll, 'at_utc': datetime.now(timezone.utc).isoformat(),
                           'run_status': run['status'], 'conclusion': run['conclusion'],
                           'successful_jobs': sum(j['conclusion'] == 'success' for j in jobs),
                           'non_success_terminal_jobs': [j['name'] for j in jobs
                               if j['status'] == 'completed' and j['conclusion'] != 'success']}
            history.append(observation)
            write(OUT / 'progress.json', {'pid': os.getpid(), 'source_commit': COMMIT,
                                          'run_id': RUN, 'history': history})
            if run['status'] == 'completed':
                success = run['conclusion'] == 'success' and all(
                    j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
                result = {'schema': 1, 'status': 'exact-source-CI-all-24-passed' if success
                          else 'exact-source-CI-terminal-non-success', 'source_commit': COMMIT,
                          'run_id': RUN, 'run_url': run['html_url'], 'successful_jobs':
                          observation['successful_jobs'], 'expected_jobs': sorted(EXPECTED),
                          'observed_at_utc': observation['at_utc'],
                          'seconds_observed': time.monotonic() - started,
                          'observer_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                          'model_calls': 0, 'gpu_trials': 0, 'CI_reruns': 0,
                          'new_registered_source_certificates': 0,
                          'original_paper_fully_reproduced': False,
                          'scope': 'Actual complete GitHub CI observation for the pinned published '
                          'source commit, including full GEMM/BMM/Linear/RoPE export/replay and adversarial tests, plus '
                          'the complete98-check six-proof ledger control job under unchanged limits. Observation performs no '
                          'new model, Lean, GPU, publication or model-service lifecycle action.'}
                write(OUT / 'results.json', result)
                write(OUT / 'manifest.json', {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                      for p in sorted(OUT.iterdir()) if p.is_file()})
                print(json.dumps(result), flush=True)
                raise SystemExit(0 if success else 1)
        except (AssertionError, RuntimeError, subprocess.TimeoutExpired, ValueError) as exc:
            history.append({'poll': poll, 'at_utc': datetime.now(timezone.utc).isoformat(),
                            'observation_error': str(exc)[:2400]})
            write(OUT / 'progress.json', {'pid': os.getpid(), 'source_commit': COMMIT,
                                          'run_id': RUN, 'history': history})
        if poll < 80:
            time.sleep(45)
    write(OUT / 'observation-ended.json', {'status': 'bounded-observation-ended',
          'source_commit': COMMIT, 'run_id': RUN, 'restart_or_rerun_authorized': False,
          'scope': 'Read actual remote run state before deciding the next action.'})


if __name__ == '__main__':
    main()
