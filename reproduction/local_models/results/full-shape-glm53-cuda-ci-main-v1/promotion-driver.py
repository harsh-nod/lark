"""Fast-forward complete six-cohort metadata after identical-code CI and public checks."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path('/tmp/lark-full-shape-glm53-cuda-results-20261113')
MAIN = Path('/home/harsh/lark')
SOURCE = OLD = '253f40923cafcaeb23829e4f1f1322fc59302efd'
PUBLISHED = 'c76f6aa79fba2ca84430527739e1480c9d4d81ba'
OUT = Path('/tmp/lark-full-shape-glm53-cuda-ci-main-v1-20261113')
PUBLICATION = Path('/tmp/lark-full-shape-glm53-cuda-publication-v1-20261113/results.json')
BASE = 'reproduction/local_models/results/'
PREFIXES = tuple(BASE + name for name in (
    'full-shape-cohort-glm53-cuda-v1', 'full-shape-comparison-six-cohorts-v1',
    'full-shape-glm53-hip-ci-main-v1', 'full-shape-deepseek-cuda-ci-main-v1',
    'full-shape-glm53-cuda-publication-v1'))
sys.path.insert(0, str(ROOT))
from reproduction.local_models import compare_full_shape as comparison  # noqa: E402


def require(ok, message):
    if not ok:
        raise ValueError(message)


def call(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True, timeout=60).strip()


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', required=True)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    target = args.target
    require(len(target) == 40 and all(c in '0123456789abcdef' for c in target), 'Concrete target required')
    require(call(['git', 'rev-parse', 'HEAD']) == target and not call(['git', 'status', '--porcelain']),
            'Candidate checkout changed')
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
            and not call(['git', 'status', '--porcelain'], MAIN), 'Main checkout changed')
    require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
    for ancestor in (OLD, PUBLISHED):
        subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, target], cwd=ROOT, check=True)
    expected = {'README.md', 'reproduction/local_models/README.md'}
    for prefix in PREFIXES:
        folder = ROOT / prefix
        manifest = read(folder / 'manifest.json')
        require(not any(p.is_symlink() for p in folder.rglob('*')), 'Metadata symlink')
        require({str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file()}
                == set(manifest) | {'manifest.json'}
                and all(sha(folder / n) == v for n, v in manifest.items()), 'Metadata inventory differs')
        expected.update(prefix + '/' + n for n in [*manifest, 'manifest.json'])
    changed = call(['git', 'diff', '--name-only', SOURCE, target]).splitlines()
    require(set(changed) == expected and len(expected) == 28,
            'Exact metadata/docs delta required; all other source/tests/Lean/workflow must match checked source')
    require(set(call(['git', 'diff', '--name-only', PUBLISHED, target]).splitlines())
            == {PREFIXES[-1] + '/' + n for n in ('results.json', 'manifest.json')},
            'Only the publication receipt may follow the anonymously verified commit')
    report = read(ROOT / PREFIXES[1] / 'results.json')
    packets = [ROOT / BASE / row['packet_id'] for row in report['inputs']]
    fresh = comparison.compare(packets)
    require({k: v for k, v in fresh.items() if k != 'created_at_utc'}
            == {k: v for k, v in report.items() if k != 'created_at_utc'}
            and comparison.markdown(fresh) == (ROOT / PREFIXES[1] / 'RESULTS.md').read_text(),
            'Complete six-cohort comparison must regenerate from raw/audit evidence')
    require(report['complete_independent_cohorts'] == 6 and report['missing_cohorts'] == []
            and report['all_six_independent_cohorts_present'] is True
            and report['original_paper_fully_reproduced'] is False, 'Six-cohort/original-paper scope differs')
    require(sum(r['recorded_counts']['verified_within_budget'] for r in report['inputs']) == 85
            and sum(r['cohort_reported_usage']['total_tokens'] for r in report['inputs']) == 15509481,
            'Actual six-cohort proof/token totals differ')
    glm = next(r for r in report['inputs'] if r['model'] == 'zai-org/GLM-5.3' and r['source_language'] == 'cuda')
    require(glm['recorded_counts'] == {'cases': 17, 'verified_within_budget': 16, 'budget_exhausted': 1,
            'first_response_verified': 0, 'first_actual_lean_check_verified': 11, 'actual_lean_checks': 25,
            'model_requests': 123, 'response_files': 123, 'raw_files': 1059, 'audit_files': 395,
            'additional_fresh_kernel_checks': 32}
            and glm['cohort_reported_usage'] == {'prompt_tokens': 2060353, 'completion_tokens': 201751,
                                                'total_tokens': 2262104}
            and glm['levels']['level1']['verified_within_budget'] == 11
            and glm['levels']['level2']['verified_within_budget'] == 5,
            'Completed GLM CUDA counts/usage/denominators differ')
    binding = read(ROOT / PREFIXES[1] / 'binding.json')
    require(binding['driver_source_checkpoint'] == SOURCE
            and binding['driver_sha256'] == report['comparison_driver_sha256']
            == sha(ROOT / binding['driver_source_path'])
            and binding['input_response_usage_records_checked'] == 782
            and binding['input_raw_files_checked'] == 6784 and binding['input_audit_files_checked'] == 2493
            and binding['recorded_additional_fresh_kernel_checks'] == 170
            and binding['fresh_lean_checks_by_comparison'] == binding['model_calls_by_comparison']
            == binding['gpu_trials_by_comparison'] == 0
            and binding['original_paper_fully_reproduced'] is False, 'Comparison binding differs')
    stop = read(ROOT / PREFIXES[0] / 'lifecycle/stop.json')
    require(stop['container_id'] == '167544c9b247f421ab5747d75c6dd8b2a5b63ed1554e7dfa10857cd956a7b886'
            and stop['running'] is False and stop['container_exit_code']
            == stop['other_container_stop_commands_issued'] == stop['model_calls_by_lifecycle_check'] == 0,
            'Exact-owned GLM completed shutdown differs')
    publication = read(PUBLICATION)
    require(publication == read(ROOT / PREFIXES[-1] / 'results.json')
            and publication['source_commit'] == PUBLISHED and publication['tls_verification'] is True
            and publication['authorization_header'] is False
            and publication['all_downloads_match_committed_bytes'] is True
            and publication['original_paper_fully_reproduced'] is False, 'Publication receipt differs')
    published = set(call(['git', 'diff', '--name-only', SOURCE, PUBLISHED]).splitlines())
    require(len(published) == len(publication['downloaded_files']) == 26
            and {r['path'] for r in publication['downloaded_files']} == published
            and all(r['http_status'] == 200 and r['curl_ssl_verify_result'] == 0
                    and r['tls_verification'] is True and r['authorization_header'] is False
                    and r['matches_committed_bytes'] is True and sha(ROOT / r['path']) == r['sha256']
                    and (ROOT / r['path']).stat().st_size == r['bytes'] for r in publication['downloaded_files'])
            and publication['total_downloaded_bytes'] == sum(r['bytes'] for r in publication['downloaded_files']),
            'Every public file must match its anonymous TLS download')
    ci = json.loads(call(['gh', 'run', 'view', '43415091796', '--repo', 'harsh-nod/lark',
                         '--json', 'status,conclusion,headSha,jobs,url']))
    prior = read(ROOT / BASE / 'full-shape-deepseek-cuda-ci-main-v1/main-ci.json')
    names = {j['name'] for j in prior['jobs']}
    require(ci['headSha'] == prior['headSha'] == SOURCE and ci['status'] == 'completed'
            and ci['conclusion'] == 'success' and len(ci['jobs']) == len(names) == 19
            and {j['name'] for j in ci['jobs']} == names
            and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs']),
            'All nineteen actual identical-code source CI jobs must pass')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
            'Remote main changed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/full-shape-glm53-cuda-results']))
            ['object']['sha'] == target, 'Published candidate branch differs')
    if args.check_only:
        print(json.dumps({'status': 'GLM-CUDA-six-cohort-metadata-main-preflight-passed', 'source_ci_jobs': 19,
                          'metadata_docs_files': len(expected), 'anonymous_files': 26,
                          'complete_independent_cohorts': 6, 'original_paper_fully_reproduced': False}))
        return
    OUT.mkdir(exist_ok=False)
    state = {'schema': 1, 'status': 'GLM-CUDA-six-cohort-main-gates-passed-update-pending',
             'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
             'published_evidence_checkpoint': PUBLISHED, 'old_main': OLD, 'promoted_commit': target,
             'source_ci': ci, 'changed_paths': changed, 'checks': {
                 'all19_actual_identical_code_source_jobs_success': True,
                 'entire_nonmetadata_tree_byte_identical_to_checked_source': True,
                 'six_complete_cohorts_usage_and_fresh_proof_bindings_regenerated': True,
                 'all26_published_files_anonymous_TLS_verified': True,
                 'exact_owned_GLM_CUDA_stopped_after_fresh_audit': True,
                 'six_of_six_not_paper_completion': True, 'clean_main_and_candidate': True,
                 'ancestry_verified': True}, 'model_calls_by_promotion': 0,
             'fresh_lean_checks_by_promotion': 0, 'gpu_trials_by_promotion': 0,
             'original_paper_fully_reproduced': False, 'helper_sha256': sha(Path(__file__))}
    write(OUT / 'progress.json', state)
    write(OUT / 'update.json', {'sha': target, 'force': False})
    state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    require(state['remote_update']['object']['sha'] == target, 'Remote main update differs')
    state['status'] = 'GLM-CUDA-six-cohort-remote-main-fast-forwarded-local-pending'
    write(OUT / 'progress.json', state)
    state['local_merge'] = call(['git', 'merge', '--ff-only', target], MAIN)
    subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', target, OLD], cwd=ROOT, check=True)
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == target
            and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs after fast-forward')
    state['status'] = 'GLM-CUDA-six-cohort-metadata-main-fast-forward-complete'
    write(OUT / 'results.json', state)
    print(json.dumps({'status': state['status'], 'main': target, 'source_ci_jobs': 19,
                      'complete_independent_cohorts': 6, 'original_paper_fully_reproduced': False}))


if __name__ == '__main__':
    main()
