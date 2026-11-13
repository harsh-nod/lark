"""Archive the already recorded DeepSeek CUDA runtime setup without reruns."""
import argparse
from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile

ROOT = Path('/tmp/lark-full-shape-cuda-models-20261113')
RUNTIME = Path('/tmp/lark-full-shape-deepseek-cuda-runtime-20261113')
SUCCESSOR = Path('/tmp/lark-deepseek-cuda-successor-v1-20261113')
PREPARED = Path('/tmp/lark-full-shape-cuda-model-preflight-v1-20261113')
SOURCE = '1b22551bc295431707dc81288a57ac9a2e6f9475'
CONTROLLER_SHA = '05438858483e7f0369e6342ecb9ab0d1f6a6820b982a8dcea270ddb3813f34b1'
CONTAINER_ID = '5c6f1fd1b4ae3b5d3624ac390786f8e8aa83622b05c1799a5b12cc5a10b63619'
sys.path.insert(0, str(ROOT))
from reproduction.local_models import full_shape_run as run


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def snapshot(runtime):
    require(not any(path.is_symlink() for path in runtime.rglob('*')), 'Runtime contains a symlink')
    files = {'runtime/' + str(path.relative_to(runtime)): path.read_bytes() for path in sorted(runtime.rglob('*')) if path.is_file()}
    for name in ('full_shape_run.py', 'full_shape.py', 'cuda_shape.py', 'client.py', 'checkpoint.py'):
        data = (ROOT / 'reproduction/local_models' / name).read_bytes()
        committed = subprocess.check_output(['git', 'show', SOURCE + ':reproduction/local_models/' + name], cwd=ROOT, timeout=30)
        require(data == committed, 'Controller file differs from its checked source: ' + name)
        files['controller/' + name] = data
    for name in ('remote-launch.py', 'remote-preflight-single-launch.log', 'owned-service-readiness.log', 'ready-record-fetch.log'):
        files['launch/' + name] = (SUCCESSOR / name).read_bytes()
    helper = Path('/tmp/lark-run-deepseek-cuda-successor-20261113.py')
    require(run.sha(helper) == '851b5d201fdae70e181a08360877373c99b304310d069340ba2af719490a529d', 'Pinned successor implementation changed')
    files['controller/successor.py'] = helper.read_bytes()
    return files


def validate(runtime):
    server, context, warmup, weights = (read(runtime / name) for name in ('server-ready.json', 'context-results.json', 'warmup-summary.json', 'checkpoint.json'))
    require(server['status'] == 'ready' and server['container_id'] == CONTAINER_ID and server['container_name'] == 'lark-full-shape-deepseek-cuda-20261113' and server['gpu_ids'] == ['2', '3', '4', '5'] and server['tensor_parallel'] == 4 and server['endpoint'] == 'http://127.0.0.1:19086/v1/chat/completions', 'Recorded owned ready-service identity differs')
    require(server['model'] == 'deepseek-ai/DeepSeek-V4.1-Flash-1017' and server['revision'] == run.MODELS[server['model']] and server['image'] == run.IMAGE and server['max_model_len'] == 65536, 'Pinned model/image/context differs')
    require(server['runner_sha256'] == run.sha(runtime / 'serve_deepseek.py') == '743aadb69c9a102bb05aec7e3e26cacb7cd1712648b1cb6a9e271ccaca785b9f' and server['checkpoint_record_sha256'] == run.sha(runtime / 'checkpoint.json') == 'da3d41868c3e4f7eefc5c73b36d6e1dcc61f7274d83a754f6b3df254b80ea3f3', 'Launcher/checkpoint record binding differs')
    require(server['docker_command'] == read(runtime / 'expected-docker-command.json'), 'Actual inference arguments differ from staged successful configuration')
    require(weights['status'] == 'verified-download' and weights['fresh_validation_only'] is True and len(weights['weights']) == 48 and len(weights['supporting_files']) == 31 and weights['downloaded_weight_bytes'] == weights['model_calls'] == 0, 'Cached revalidation counts/scope differ')
    usage = {'prompt_tokens': 47, 'total_tokens': 69, 'completion_tokens': 22, 'completion_tokens_details': {'reasoning_tokens': 15}}
    require(warmup['status'] == 'warmup-passed' and warmup['content'] == 'LARK_READY' and warmup['usage'] == usage and warmup['actual_generation_requests'] == 1 and warmup['model_proof_attempts'] == warmup['external_api_spend_usd'] == 0, 'Recorded non-proof warmup differs')
    request, response, receipt = (read(runtime / 'warmup' / name) for name in ('request.json', 'response.json', 'receipt.json'))
    require(request == {'model': server['model'], 'messages': [{'role': 'system', 'content': 'Reply with exactly LARK_READY and nothing else.'}, {'role': 'user', 'content': 'LARK_READY'}], 'temperature': 0, 'max_tokens': 256, 'seed': 0, 'stream': False, 'thinking_token_budget': 64}, 'Warmup request differs from the staged protocol')
    require(response['choices'][0]['message']['content'].strip() == 'LARK_READY' and response['usage'] == receipt['usage'] == usage and receipt['request_sha256'] == run.sha(runtime / 'warmup/request.json') and receipt['response_sha256'] == run.sha(runtime / 'warmup/response.json') and receipt['model'] == server['model'] and receipt['endpoint'] == server['endpoint'] and receipt['external_api_spend_usd'] == 0, 'Warmup response/receipt byte binding differs')
    require(context['status'] == 'all-seventeen-full-size-initial-contexts-fit' and context['source_language'] == 'cuda' and context['runner_sha256'] == CONTROLLER_SHA == run.sha(Path(run.__file__)) and context['driver_sha256'] == run.sha(runtime / 'context-and-warmup.py') == '6895d54e6c5205b8a72fa553b34f9baf7ac88349cc6292f9fc564abd680fff9c' and context['preparation_manifest_sha256'] == run.sha(PREPARED / 'manifest.json') == run.CUDA_PREPARATION_SHA256, 'CUDA context/controller/source binding differs')
    sources = run.verify_preparation(PREPARED)
    require([row['case'] for row in context['cases']] == [row[0] for row in run.full_shape.benchmark.CASES], 'Exact seventeen-case context roster required')
    for row in context['cases']:
        folder = runtime / 'context' / row['case']
        req, res, rec = (read(folder / name) for name in ('request.json', 'response.json', 'receipt.json'))
        fixed = read(PREPARED / 'cases' / row['case'] / 'request.json')
        _, catalogue = run.library_context(row['case'], sources)
        messages = run.messages(fixed, catalogue, [], 'No candidate yet. Inspect generic libraries as needed and prove all four fixed goals.', '', {'model_requests': 16, 'proof_checks': 3, 'library_reads': 8})
        require(req == {'model': server['model'], 'messages': messages, 'add_generation_prompt': True} and row['messages_sha256'] == sha(run.encoded(messages)), 'Context prompt does not regenerate: ' + row['case'])
        require(row['input_tokens'] == rec['input_tokens'] == res['count'] == len(res['tokens']) and row['reported_context'] == rec['reported_context'] == res['max_model_len'] == 65536, 'Tokenizer counts/context differ: ' + row['case'])
        require(rec['request_sha256'] == run.sha(folder / 'request.json') and rec['response_sha256'] == run.sha(folder / 'response.json') and rec['model_inference_calls'] == 0, 'Tokenizer byte/call binding differs: ' + row['case'])
        require(row['input_tokens'] + run.PROTOCOL['max_tokens'] + run.PROTOCOL['context_margin'] <= 65536, 'Initial context exceeds common proof budget')
    require(context['max_initial_prompt_tokens'] == max(row['input_tokens'] for row in context['cases']) == 23001, 'Initial context maximum differs')
    launch = read(SUCCESSOR / 'remote-preflight-single-launch.log')
    require(launch['status'] == 'exact-owned-DeepSeek-CUDA-container-started-readiness-pending' and launch['container_id'] == CONTAINER_ID and launch['expected_docker_command'] == server['docker_command'] and launch['launch_process_exit_code'] == 0, 'Recorded single owned launch differs')
    require((SUCCESSOR / 'ready-record-fetch.log').read_bytes() == (runtime / 'server-ready.json').read_bytes(), 'Fetched readiness bytes differ')
    return server, context, warmup, weights


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runtime', type=Path, default=RUNTIME)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    runtime, output = args.runtime.resolve(), args.output.resolve()
    require(not output.exists() and not any((path / '.git').exists() for path in (output, *output.parents)), 'Fresh outside-Git output required')
    require(not output.is_relative_to(runtime), 'Output must be outside the input')
    server, context, warmup, weights = validate(runtime)
    files = snapshot(runtime)
    if args.check_only:
        print(json.dumps({'status': 'DeepSeek-CUDA-runtime-packet-preflight-passed', 'files': len(files), 'context_cases': 17, 'max_initial_prompt_tokens': 23001, 'model_calls_by_validation': 0, 'GPU_actions': 0, 'fresh_lean_checks': 0}))
        return
    output.mkdir(parents=True, exist_ok=False)
    with (output / 'runtime.tar.gz').open('wb') as target, gzip.GzipFile(fileobj=target, mode='wb', mtime=0, filename='') as compressed:
        with tarfile.open(fileobj=compressed, mode='w') as archive:
            for name, data in sorted(files.items()):
                item = tarfile.TarInfo(name)
                item.size, item.mode = len(data), 0o644
                archive.addfile(item, io.BytesIO(data))
    inventory = {name: sha(data) for name, data in sorted(files.items())}
    write(output / 'runtime-files.json', inventory)
    with tarfile.open(output / 'runtime.tar.gz', 'r:gz') as archive:
        members = archive.getmembers()
        require(len(members) == len(files) and {item.name for item in members} == set(files) and all(item.isfile() and sha(archive.extractfile(item).read()) == inventory[item.name] for item in members), 'Written runtime archive differs')
    require({name: sha(data) for name, data in snapshot(runtime).items()} == inventory, 'Runtime setup bytes changed during capture')
    report = {'schema': 1, 'status': 'recorded-deepseek-CUDA-runtime-warmup-and-seventeen-contexts-bound', 'packaged_at_utc': datetime.now(timezone.utc).isoformat(), 'source_language': 'cuda', 'model': server['model'], 'revision': server['revision'], 'image': server['image'], 'container_id': CONTAINER_ID, 'gpu_ids': ['2', '3', '4', '5'], 'host': 'mi350', 'tensor_parallel': 4, 'endpoint': server['endpoint'], 'ready_utc': server['ready_utc'], 'preparation_manifest_sha256': context['preparation_manifest_sha256'], 'controller_source_checkpoint': SOURCE, 'controller_sha256': CONTROLLER_SHA, 'checkpoint_record_sha256': server['checkpoint_record_sha256'], 'checkpoint_weight_files': 48, 'checkpoint_support_files': 31, 'recorded_cached_revalidation_seconds': weights['validation_seconds'], 'weight_bytes_downloaded_by_recorded_revalidation': 0, 'recorded_owned_service_launches': 1, 'warmup_generation_requests': 1, 'warmup_usage': warmup['usage'], 'warmup_excluded_from_proof_metrics': True, 'context_cases': 17, 'max_initial_prompt_tokens': 23001, 'common_proof_context_limit': 65536, 'advertised_server_context_limit': 65536, 'all_recorded_context_prompts_regenerated_from_frozen_tasks': True, 'source_checked_archive_files': len(files), 'archive_uncompressed_bytes': sum(map(len, files.values())), 'model_calls_by_archival': 0, 'GPU_lifecycle_actions_by_archival': 0, 'gpu_kernel_trials': 0, 'fresh_lean_checks_by_archival': 0, 'new_registered_source_certificates': 0, 'model_proof_successes_claimed_by_setup': 0, 'external_api_spend_usd': 0, 'original_paper_fully_reproduced': False, 'scope': 'Historical exact-owned ready-service, one non-proof warmup, seventeen tokenizer records and cached checkpoint revalidation, bound to the single guarded launch. No weights rehashed/downloaded, inference/Lean rerun or GPU lifecycle action by capture. Historical staging plans remain unchanged in the archive. Proof outcomes and final lifecycle belong to the separate complete cohort packet. CUDA identifies proof-task source language; serving uses MI350X.'}
    write(output / 'results.json', report)
    shutil.copyfile(__file__, output / 'package.py')
    write(output / 'manifest.json', {path.name: run.sha(path) for path in sorted(output.iterdir()) if path.is_file()})
    print(json.dumps({'status': 'DeepSeek-CUDA-runtime-packet-complete', 'files': len(files), 'uncompressed_bytes': report['archive_uncompressed_bytes'], 'model_calls_by_capture': 0, 'GPU_actions_by_capture': 0, 'fresh_lean_checks': 0}))


if __name__ == '__main__':
    main()
