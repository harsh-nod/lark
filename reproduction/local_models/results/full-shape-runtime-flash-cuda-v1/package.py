from datetime import datetime, timezone
import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import sys
import tarfile

ROOT = Path('/tmp/lark-full-shape-flash-runtimes-20261113')
sys.path.insert(0, str(ROOT))
from reproduction.local_models import full_shape_run as run


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


records = []
for kind, runtime, controller_root, prepared, cid, gpus, port, controller_sha, checkpoint in (
    ('hip', '/tmp/lark-full-shape-flash-runtime-20261113', '/tmp/lark-full-shape-models-20261112',
     '/tmp/lark-full-shape-model-preflight-v2-20261112',
     '324b3f46004bac687d261c1ce9ca08c8d02591cdc67210b5f30726bcb9ee8f1b', ['2','3'], 19087,
     '0e49b6ce519a2af91c81ee60419adcf37357a71fdf904a772dab0cd279368aef',
     'bb114d8ae61183320242fa5f4463d0cfc727bcd1'),
    ('cuda', '/tmp/lark-full-shape-flash-cuda-runtime-20261113', '/tmp/lark-full-shape-cuda-models-20261113',
     '/tmp/lark-full-shape-cuda-model-preflight-v1-20261113',
     'b362a94e7835930941dbda78b01b13aef5a84c890d80a812555e2bf70ab76c83', ['4','5'], 19088,
     '05438858483e7f0369e6342ecb9ab0d1f6a6820b982a8dcea270ddb3813f34b1',
     '1b22551bc295431707dc81288a57ac9a2e6f9475'),
):
    runtime, controller_root, prepared = map(Path, (runtime, controller_root, prepared))
    server = read(runtime/'server-ready.json')
    context = read(runtime/'context-results.json')
    warmup = read(runtime/'warmup-summary.json')
    weights = read(runtime/'checkpoint.json')
    assert server['status'] == 'ready' and server['container_id'] == cid
    assert server['gpu_ids'] == gpus and server['endpoint'] == f'http://127.0.0.1:{port}/v1/chat/completions'
    assert server['model'] == 'zai-org/GLM-5.3-Flash'
    assert server['revision'] == run.MODELS[server['model']] and server['image'] == run.IMAGE
    assert server['runner_sha256'] == sha((runtime/'serve.py').read_bytes())
    assert server['checkpoint_record_sha256'] == sha((runtime/'checkpoint.json').read_bytes())
    assert weights['status'] == 'verified-download' and weights['fresh_validation_only'] is True
    assert len(weights['weights']) == 62 and len(weights['supporting_files']) == 9
    assert weights['downloaded_weight_bytes'] == weights['model_calls'] == 0
    assert warmup['status'] == 'warmup-passed' and warmup['content'] == 'LARK_READY'
    assert warmup['usage'] == {'prompt_tokens':26,'total_tokens':31,'completion_tokens':5,
                               'completion_tokens_details':{'reasoning_tokens':0}}
    assert context['status'] == 'all-seventeen-full-size-initial-contexts-fit'
    assert context.get('source_language', 'hip') == kind
    assert context['runner_sha256'] == controller_sha
    assert context['driver_sha256'] == sha((runtime/'context-and-warmup.py').read_bytes())
    assert sha((controller_root/'reproduction/local_models/full_shape_run.py').read_bytes()) == controller_sha
    assert context['preparation_manifest_sha256'] == run.sha(prepared/'manifest.json')
    sources = run.verify_preparation(prepared)
    assert [x['case'] for x in context['cases']] == [x[0] for x in run.full_shape.benchmark.CASES]
    for row in context['cases']:
        name = row['case']
        folder = runtime/'context'/name
        req, res, receipt = (read(folder/n) for n in ('request.json','response.json','receipt.json'))
        fixed = read(prepared/'cases'/name/'request.json')
        _, catalogue = run.library_context(name, sources)
        messages = run.messages(fixed, catalogue, [],
            'No candidate yet. Inspect generic libraries as needed and prove all four fixed goals.', '',
            {'model_requests':16,'proof_checks':3,'library_reads':8})
        assert req == {'model':server['model'],'messages':messages,'add_generation_prompt':True}
        assert row['messages_sha256'] == sha(run.encoded(messages))
        assert row['input_tokens'] == receipt['input_tokens'] == res['count'] == len(res['tokens'])
        assert row['reported_context'] == receipt['reported_context'] == res['max_model_len'] == 131072
        assert receipt['request_sha256'] == sha((folder/'request.json').read_bytes())
        assert receipt['response_sha256'] == sha((folder/'response.json').read_bytes())
        assert receipt['model_inference_calls'] == 0
        assert row['input_tokens'] + run.PROTOCOL['max_tokens'] + run.PROTOCOL['context_margin'] <= 65536
    assert context['max_initial_prompt_tokens'] == max(x['input_tokens'] for x in context['cases'])
    files = {'runtime/'+str(p.relative_to(runtime)):p.read_bytes()
             for p in sorted(runtime.rglob('*')) if p.is_file()}
    for name in ('full_shape_run.py','full_shape.py','client.py','checkpoint.py') + (('cuda_shape.py',) if kind=='cuda' else ()):
        files['controller/'+name] = (controller_root/'reproduction/local_models'/name).read_bytes()
    out = ROOT/'reproduction/local_models/results'/f'full-shape-runtime-flash-{kind}-v1'
    out.mkdir(exist_ok=False)
    with (out/'runtime.tar.gz').open('wb') as target, gzip.GzipFile(fileobj=target,mode='wb',mtime=0,filename='') as compressed:
        with tarfile.open(fileobj=compressed,mode='w') as archive:
            for name, data in sorted(files.items()):
                info = tarfile.TarInfo(name);info.size=len(data);info.mode=0o644
                archive.addfile(info,io.BytesIO(data))
    inventory = {n:sha(b) for n,b in sorted(files.items())}
    write(out/'runtime-files.json',inventory)
    # Check the actual written archive rather than only its intended inputs.
    with tarfile.open(out/'runtime.tar.gz','r:gz') as archive:
        members = archive.getmembers()
        assert len(members) == len(files) and {m.name for m in members} == set(files)
        assert all(m.isfile() and sha(archive.extractfile(m).read()) == inventory[m.name] for m in members)
    report = {'schema':1,'status':'recorded-flash-runtime-warmup-and-seventeen-contexts-bound',
        'packaged_at_utc':datetime.now(timezone.utc).isoformat(),'source_language':kind,
        'model':server['model'],'revision':server['revision'],'image':server['image'],
        'container_id':cid,'gpu_ids':gpus,'host':'mi350','tensor_parallel':2,
        'endpoint':server['endpoint'],'ready_utc':server['ready_utc'],
        'preparation_manifest_sha256':context['preparation_manifest_sha256'],
        'controller_source_checkpoint':checkpoint,'controller_sha256':controller_sha,
        'checkpoint_record_sha256':server['checkpoint_record_sha256'],
        'checkpoint_weight_files':62,'checkpoint_support_files':9,
        'shared_checkpoint_revalidation_seconds':weights['validation_seconds'],
        'weight_bytes_downloaded_by_recorded_revalidation':0,
        'warmup_generation_requests':1,'warmup_usage':warmup['usage'],
        'warmup_excluded_from_proof_metrics':True,'context_cases':17,
        'max_initial_prompt_tokens':context['max_initial_prompt_tokens'],
        'common_proof_context_limit':65536,'advertised_server_context_limit':131072,
        'all_recorded_context_prompts_regenerated_from_frozen_tasks':True,
        'source_checked_archive_files':len(files),'archive_uncompressed_bytes':sum(map(len,files.values())),
        'model_calls_by_archival':0,'gpu_kernel_trials':0,'fresh_lean_checks_by_archival':0,
        'new_registered_source_certificates':0,'model_proof_successes_claimed_by_setup':0,
        'external_api_spend_usd':0,'original_paper_fully_reproduced':False,
        'scope':'Historical ready-service, one non-proof warmup, tokenizer records and cached checkpoint revalidation. Two TP2 replicas share the same already-revalidated weights; this archive does not rehash GPU-host weights again. Proof results and later service lifecycle remain in separate complete cohort packets. CUDA denotes proof-task source language; no CUDA kernel execution or NVIDIA measurement.'}
    write(out/'results.json',report)
    shutil.copyfile(__file__,out/'package.py')
    write(out/'manifest.json',{p.name:sha(p.read_bytes()) for p in sorted(out.iterdir()) if p.is_file()})
    records.append({'language':kind,'files':len(files),'bytes':sum(map(len,files.values())),
                    'max_initial_prompt_tokens':context['max_initial_prompt_tokens']})
print(json.dumps({'status':'both-flash-runtime-packets-complete','packets':records}))
