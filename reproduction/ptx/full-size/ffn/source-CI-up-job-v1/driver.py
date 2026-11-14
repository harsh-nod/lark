"""Capture an original terminal FFN-source CI job; never rerun it."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--job', type=int, required=True)
    parser.add_argument('--kind', choices=['up', 'ledger'], required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output
    out.mkdir(exist_ok=False)
    (out / 'driver.py').write_bytes(Path(__file__).read_bytes())
    env = dict(os.environ, HTTPS_PROXY='socks5://127.0.0.1:19089')
    for name, suffix in [('job.json', ''), ('logs.raw', '/logs')]:
        row = subprocess.run(['gh', 'api', f'repos/harsh-nod/lark/actions/jobs/{args.job}' + suffix],
                             env=env, capture_output=True, timeout=90)
        (out / name).write_bytes(row.stdout)
        (out / (name + '.stderr')).write_bytes(row.stderr)
        assert row.returncode == 0, row.stderr
        if name == 'job.json':
            job = json.loads(row.stdout)
            assert job['run_id'] == 43580112712 and job['head_sha'] == '8309738beff6486be282cd92b18177eaf9b232ab'
            assert job['status'] == 'completed'
            assert job['name'] == ('ptx-matrix' if args.kind == 'up' else 'paper-ledger')
            assert job['conclusion'] == ('success' if args.kind == 'up' else 'failure')
    raw = (out / 'logs.raw').read_text()
    result = {'status': 'exact-source-up-stage-CI-job-passed' if args.kind == 'up'
              else 'original-FFN-branch-ledger-job-failed',
              'source_commit': job['head_sha'], 'run_id': job['run_id'], 'job_id': args.job,
              'whole_workflow_success_claim': False, 'CI_reruns': 0,
              'compiled_FFN_pipeline_proofs': 0, 'GPU_trials': 0, 'model_calls': 0,
              'original_paper_fully_reproduced': False}
    if args.kind == 'up':
        steps = [s for s in job['steps'] if s['name'] ==
            'Prove the complete FFN up stage and independent reference with fresh owned modules']
        assert len(steps) == 1 and steps[0]['conclusion'] == 'success'
        records = []
        for line in raw.splitlines():
            start = line.find('{"status": "exact-full-size-FFN-up-launch-reference-race-frame-passed"')
            if start >= 0:
                records.append(json.loads(line[start:]))
        assert len(records) == 1
        report = records[0]
        assert len(report['module_checks']) == 10
        assert all(c['exit_code'] == 0 and c['timed_out'] is False for c in report['module_checks'])
        assert len(report['axiom_audits']) == 220
        assert set(a for names in report['axiom_audits'].values() for a in names) <= {'propext', 'Classical.choice', 'Quot.sound'}
        assert report['limits'] == {'maxRecDepth': 10000, 'maxHeartbeats': 2000000,
            'per_Lean_process_seconds': 180, 'source_import_build_seconds': 600}
        assert report['Lean_sha256'] == '92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023'
        assert report['all_own_modules_fresh'] is True
        assert report['compiled_FFN_up_stage_correctness_proofs'] == 1
        assert report['compiled_FFN_down_stage_correctness_proofs'] == report['compiled_FFN_pipeline_correctness_proofs'] == 0
        (out / 'up-checker-result.json').write_text(json.dumps(report, indent=2) + '\n')
        result.update(up_step=steps[0], axiom_audits=220, checker_seconds=report['total_seconds'],
                      full_up_stage_proofs=1, fresh_owned_libraries=9, fresh_Main=1)
    else:
        result.update(failed_steps=[s for s in job['steps'] if s['conclusion'] == 'failure'],
            diagnostics=[line for line in raw.splitlines() if '##[error]' in line or 'Exit status:' in line],
            complete_control_logs_not_dumped_by_this_older_workflow=True)
    (out / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    (out / 'manifest.json').write_text(json.dumps({p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
