"""Archive the already recorded GLM CUDA runtime setup without reruns."""
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
RUNTIME = Path('/tmp/lark-full-shape-glm53-cuda-runtime-20261113')
SUCCESSOR = Path('/tmp/lark-glm-cuda-successor-v1-20261113')
PREPARED = Path('/tmp/lark-full-shape-cuda-model-preflight-v1-20261113')
SOURCE = '1b22551bc295431707dc81288a57ac9a2e6f9475'
CONTROLLER_SHA = '05438858483e7f0369e6342ecb9ab0d1f6a6820b982a8dcea270ddb3813f34b1'
CONTAINER_ID = '167544c9b247f421ab5747d75c6dd8b2a5b63ed1554e7dfa10857cd956a7b886'
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
    for name in ('retained-service-check.log', 'retained-service-record.log', 'archive-HIP.log', 'CUDA-warmup-context.log'):
        files['sequential-reuse/' + name] = (SUCCESSOR / name).read_bytes()
    helper = Path('/tmp/lark-run-glm-cuda-successor-20261113.py')
    require(run.sha(helper) == 'e10ff548d11ae71d6e5e8e169435ee3a7552597d4a1dd274e91929487e084237', 'Pinned successor implementation changed')
    files['controller/successor.py'] = helper.read_bytes()
    retention = Path('/tmp/lark-record-finished-glm-reuse-20261113.py')
    require(run.sha(retention) == '5df95c5add1eade77dbbb4793df48e45070bb93fb36cd3b4201e9080a20721ec', 'Pinned retention implementation changed')
    files['controller/retained-service.py'] = retention.read_bytes()
    return files


def validate(runtime):
    server, context, warmup, weights = (read(runtime / name) for name in ('server-ready.json', 'context-results.json', 'warmup-summary.json', 'checkpoint.json'))
    require(server['status'] == 'ready' and server['container_id'] == CONTAINER_ID and server['container_name'] == 'lark-full-shape-glm53-20261113' and server['gpu_ids'] == ['0', '1', '6', '7'] and server['tensor_parallel'] == 4 and server['endpoint'] == 'http://127.0.0.1:19085/v1/chat/completions', 'Recorded owned ready-service identity differs')
    require(server['model'] == 'zai-org/GLM-5.3' and server['revision'] == run.MODELS[server['model']] and server['image'] == run.IMAGE and server['max_model_len'] == 65536, 'Pinned model/image/context differs')
    require(server['runner_sha256'] == run.sha(runtime / 'serve_glm.py') == 'd33057f30f17168a913015f45e479b11431ff1928030264d9afeb6c2262934c8' and server['checkpoint_record_sha256'] == run.sha(runtime / 'checkpoint.json') == 'f2d85e77bc2fe2dbdc311b2f1e4db55e1d46c0d79cddbcc8346102c7ef343cdf', 'Launcher/checkpoint record binding differs')
    require(run.sha(runtime / 'server-ready.json') == '2b2827d1b706072abd2c2b4e9d004c5eb2d4cf7eec93205a2287a3855765570a', 'Historical original readiness/configuration bytes differ')
    require(weights['status'] == 'verified-download' and weights['fresh_validation_only'] is True and len(weights['weights']) == 141 and len(weights['supporting_files']) == 8 and weights['downloaded_weight_bytes'] == weights['model_calls'] == 0, 'Cached revalidation counts/scope differ')
    usage = {'prompt_tokens': 26, 'total_tokens': 55, 'completion_tokens': 29, 'completion_tokens_details': {'reasoning_tokens': 24}}
    require(warmup['status'] == 'warmup-passed' and warmup['content'] == 'LARK_READY' and warmup['usage'] == usage and warmup['actual_generation_requests'] == 1 and warmup['model_proof_attempts'] == warmup['external_api_spend_usd'] == 0, 'Recorded non-proof warmup differs')
    request, response, receipt = (read(runtime / 'warmup' / name) for name in ('request.json', 'response.json', 'receipt.json'))
    require(request == {'model': server['model'], 'messages': [{'role': 'system', 'content': 'Reply with exactly LARK_READY and nothing else.'}, {'role': 'user', 'content': 'LARK_READY'}], 'temperature': 0, 'max_tokens': 256, 'seed': 0, 'stream': False, 'reasoning_effort': 'low', 'thinking_token_budget': 64}, 'Warmup request differs from the staged protocol')
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
    require(context['max_initial_prompt_tokens'] == max(row['input_tokens'] for row in context['cases']) == 22496, 'Initial context maximum differs')
    reuse = read(runtime / 'service-reuse.json')
    published = Path('/home/harsh/lark/reproduction/local_models/results/full-shape-cohort-glm53-hip-v1/lifecycle/service-reuse.json')
    require((runtime / 'service-reuse.json').read_bytes() == published.read_bytes(), 'Sequential service receipt differs from published HIP completion')
    require(reuse['status'] == 'completed-audited-GLM-HIP-service-drained-and-retained' and reuse['container_id'] == CONTAINER_ID and reuse['running'] is True and reuse['retained_for_sequential_cohort'] is True and reuse['inference_configuration_unchanged'] is True and reuse['server_record_sha256'] == run.sha(runtime / 'server-ready.json'), 'Retained exact-owned service binding differs')
    require(reuse['docker_stop_commands_issued'] == reuse['gpu_services_started'] == reuse['model_calls_by_lifecycle_check'] == 0 and all(value == 0 for values in reuse['drained_metrics'].values() for value in values), 'Retained-service drain/lifecycle scope differs')
    require(reuse['completion_binding']['verified_model_proofs'] == 15 and reuse['completion_binding']['model_requests'] == 123 and reuse['completion_binding']['replay']['fresh_kernel_checks'] == 30, 'Preceding audited HIP binding differs')
    require(read(SUCCESSOR / 'retained-service-record.log') == reuse, 'Successor retained-service log differs')
    require(read(SUCCESSOR / 'CUDA-warmup-context.log') == {'status': 'warmup-and-context-preflight-passed', 'context_cases': 17, 'max_initial_prompt_tokens': 22496, 'warmup_usage': usage}, 'Recorded successor CUDA warmup/context completion differs')
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
        print(json.dumps({'status': 'GLM-CUDA-runtime-packet-preflight-passed', 'files': len(files), 'context_cases': 17, 'max_initial_prompt_tokens': 22496, 'model_calls_by_validation': 0, 'GPU_actions': 0, 'fresh_lean_checks': 0}))
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
    report = {'schema': 1, 'status': 'recorded-deepseek-CUDA-runtime-warmup-and-seventeen-contexts-bound', 'packaged_at_utc': datetime.now(timezone.utc).isoformat(), 'source_language': 'cuda', 'model': server['model'], 'revision': server['revision'], 'image': server['image'], 'container_id': CONTAINER_ID, 'gpu_ids': ['0', '1', '6', '7'], 'host': 'mi350', 'tensor_parallel': 4, 'endpoint': server['endpoint'], 'historical_initial_ready_utc': server['ready_utc'], 'service_reuse_observed_at_utc': read(runtime / 'service-reuse.json')['observed_at_utc'], 'preparation_manifest_sha256': context['preparation_manifest_sha256'], 'controller_source_checkpoint': SOURCE, 'controller_sha256': CONTROLLER_SHA, 'checkpoint_record_sha256': server['checkpoint_record_sha256'], 'checkpoint_weight_files': 141, 'checkpoint_support_files': 8, 'recorded_cached_revalidation_seconds': weights['validation_seconds'], 'weight_bytes_downloaded_by_recorded_revalidation': 0, 'recorded_owned_service_launches_for_CUDA': 0, 'sequential_reuse_after_complete_audited_HIP': True, 'warmup_generation_requests': 1, 'warmup_usage': warmup['usage'], 'warmup_excluded_from_proof_metrics': True, 'context_cases': 17, 'max_initial_prompt_tokens': 22496, 'common_proof_context_limit': 65536, 'advertised_server_context_limit': 65536, 'all_recorded_context_prompts_regenerated_from_frozen_tasks': True, 'source_checked_archive_files': len(files), 'archive_uncompressed_bytes': sum(map(len, files.values())), 'model_calls_by_archival': 0, 'GPU_lifecycle_actions_by_archival': 0, 'gpu_kernel_trials': 0, 'fresh_lean_checks_by_archival': 0, 'new_registered_source_certificates': 0, 'model_proof_successes_claimed_by_setup': 0, 'external_api_spend_usd': 0, 'original_paper_fully_reproduced': False, 'scope': 'Historical exact-owned initial-ready service, fresh unchanged-configuration/drained sequential-reuse receipt after complete audited HIP, one separate CUDA non-proof warmup, seventeen CUDA tokenizer records and previously cached checkpoint revalidation. Zero new service launches for CUDA. Capture rehashes no weights and makes no model/Lean/GPU action. Historical staging plans retain their original bytes; proof outcomes/final lifecycle belong to the separate complete cohort packet. CUDA names proof-task source language on AMD serving.'}
    write(output / 'results.json', report)
    shutil.copyfile(__file__, output / 'package.py')
    write(output / 'manifest.json', {path.name: run.sha(path) for path in sorted(output.iterdir()) if path.is_file()})
    print(json.dumps({'status': 'GLM-CUDA-runtime-packet-complete', 'files': len(files), 'uncompressed_bytes': report['archive_uncompressed_bytes'], 'model_calls_by_capture': 0, 'GPU_actions_by_capture': 0, 'fresh_lean_checks': 0}))


if __name__ == '__main__':
    main()
