from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import subprocess
import requests

out = Path('/tmp/lark-native-qknorm-rope-publication-v1-20261111')
out.mkdir()
local = Path('/tmp/lark-native-qknorm-rope-public-assets-v1-20261111')
source = 'c9a7a242de6696e4c9c1aa402d7046b3db2518d9'
tag = 'native-qknorm-rope-evidence-20261111'
release = json.loads(subprocess.check_output(['gh','api','repos/harsh-nod/lark/releases/tags/'+tag]))
ref = json.loads(subprocess.check_output(['gh','api','repos/harsh-nod/lark/git/ref/tags/'+tag]))
assert release['target_commitish'] == source and ref['object']['sha'] == source
expected = json.loads((local/'SHA256.json').read_text())
expected['SHA256.json'] = {'sha256':hashlib.sha256((local/'SHA256.json').read_bytes()).hexdigest(),
                           'bytes':(local/'SHA256.json').stat().st_size}
assert len(release['assets']) == 4 and {a['name'] for a in release['assets']} == set(expected)
def fetch(asset):
    name = asset['name']
    wanted = expected[name]
    assert asset['size'] == wanted['bytes'] and asset['digest'] == 'sha256:'+wanted['sha256'],name
    result = requests.get(asset['browser_download_url'],stream=True,timeout=(20,60),
                          verify='/tmp/lark-release-upload-ca-bundle-20261111.pem')
    result.raise_for_status()
    digest,count=hashlib.sha256(),0
    for part in result.iter_content(1024*1024):
        digest.update(part);count+=len(part)
    assert count == wanted['bytes'] and digest.hexdigest() == wanted['sha256'],name
    return {'name':name,'asset_id':asset['id'],'url':asset['browser_download_url'],
            'bytes':count,'sha256':digest.hexdigest(),'github_server_digest':asset['digest'],
            'anonymous_full_body_download_verified':True,'http_status':result.status_code}
with ThreadPoolExecutor(max_workers=4) as pool:
    checked=list(pool.map(fetch,release['assets']))
run=json.loads(subprocess.check_output(['gh','api','repos/harsh-nod/lark/actions/runs/43112261267']))
jobs=json.loads(subprocess.check_output(['gh','api','repos/harsh-nod/lark/actions/runs/43112261267/jobs']))
assert run['head_sha']==source
root=Path('/tmp/lark-native-qknorm-rope-20261111')
sources=json.loads(Path('/tmp/lark-native-qknorm-rope-components-v2-20261111/source-manifest.json').read_text())
for name,h in sources.items():
    content=subprocess.check_output(['git','-C',str(root),'show',source+':'+name])
    assert hashlib.sha256(content).hexdigest()==h,name
for name,data in [('github-release.json',release),('github-tag-ref.json',ref),('github-ci-run.json',run),('github-ci-jobs.json',jobs)]:
    (out/name).write_text(json.dumps(data,indent=2)+'\n')
result={'schema':1,'status':'native-fused-qknorm-rope-public-assets-fully-downloaded-and-bound',
        'source_commit':source,'release_url':release['html_url'],'release_id':release['id'],
        'assets':checked,'total_anonymously_downloaded_bytes':sum(a['bytes'] for a in checked),
        'all_four_assets_match_local_and_github_server_digests':True,'source_files_bound_to_revision':len(sources),
        'ci_run':run['html_url'],'ci_status_at_capture':run['status'],'ci_conclusion_at_capture':run['conclusion'],
        'ci_jobs_at_capture':[{k:j[k] for k in ['name','status','conclusion']} for j in jobs['jobs']],
        'source_certificates':0,'whole_kernel_execution_proved':False,'source_reference_equality_proved':False,
        'model_calls':0,'new_gpu_trials':0,'original_paper_fully_reproduced':False}
(out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(out/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps({'status':result['status'],'assets':4,'bytes':result['total_anonymously_downloaded_bytes'],'source_files':len(sources),'ci':run['conclusion']}))
