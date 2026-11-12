import hashlib
import json
from pathlib import Path
import shutil
import ssl
import subprocess
import sys
import urllib.request

ROOT = Path('/tmp/lark-elaborated-reference-audit-20261112')
OUT = Path('/tmp/lark-elaborated-reference-publication-v3-20261112')
COMMIT = '4a4c5efbdb91965d53d5e705c911029f2b1f4a50'
PREFIX = 'reproduction/specification_validation/'
PACKET = PREFIX+'results/production-real-v1/'
OUT.mkdir(exist_ok=False)
(OUT/'packet').mkdir()
(OUT/'drivers').mkdir()
observations = []

def sha(data):
    return hashlib.sha256(data).hexdigest()

def download(name,target):
    url = 'https://raw.githubusercontent.com/harsh-nod/lark/'+COMMIT+'/'+name
    import os
    environment = dict(os.environ,NO_PROXY='',no_proxy='')
    request = subprocess.run(['curl','-q','--fail','--silent','--show-error','--location',
                              '--proto','=https','--tlsv1.2','--max-time','45',
                              '--proxy','socks5h://127.0.0.1:18028','--output',str(target),
                              '--write-out','%{http_code}\n%{url_effective}\n%{ssl_verify_result}\n',url],
                             env=environment,capture_output=True,text=True,timeout=50)
    request.check_returncode()
    status, effective, verified = request.stdout.strip().splitlines()
    data = target.read_bytes()
    if status != '200' or verified != '0' or len(data)>10_000_000:
        raise ValueError('Unexpected verified public response: '+name)
    observation = {'path':name,'url':url,'effective_url':effective,'http_status':int(status),
                   'bytes':len(data),'sha256':sha(data),'authorization_header':False,'tls_verification':True,
                   'curl_ssl_verify_result':int(verified),'transport':'verified TLS over owned SSH SOCKS tunnel'}
    local = subprocess.check_output(['git','show',COMMIT+':'+name],cwd=ROOT)
    if data != local:
        raise ValueError('Anonymous public bytes differ from committed blob: '+name)
    target.write_bytes(data)
    observations.append(observation)
    print(json.dumps({'downloaded':name,'bytes':len(data)}),flush=True)

download(PACKET+'manifest.json',OUT/'packet/manifest.json')
manifest = json.loads((OUT/'packet/manifest.json').read_text())
expected = {'source.tar.gz','source-manifest.json','evidence.tar.gz','evidence-manifest.json','results.json','packet.py'}
if set(manifest) != expected:
    raise ValueError('Unexpected public packet inventory')
for name in sorted(manifest):
    download(PACKET+name,OUT/'packet'/name)
    if sha((OUT/'packet'/name).read_bytes()) != manifest[name]:
        raise ValueError('Public packet manifest mismatch: '+name)
download(PREFIX+'check_packet.py',OUT/'drivers/check_packet.py')
shutil.copyfile(OUT/'packet/packet.py',OUT/'drivers/packet.py')
for name,command in (
    ('verification',[sys.executable,str(OUT/'packet/packet.py'),'verify','--packet',str(OUT/'packet'),
                     '--output',str(OUT/'verification')]),
    ('controls',[sys.executable,str(OUT/'drivers/check_packet.py'),'--packet',str(OUT/'packet'),
                 '--output',str(OUT/'controls')]),
):
    run = subprocess.run(command,capture_output=True,text=True,timeout=180)
    (OUT/(name+'.log')).write_text(run.stdout+run.stderr)
    if run.returncode:
        raise ValueError('Anonymous public packet '+name+' failed; inspect saved log')
result = {'schema':1,'status':'anonymous-public-production-reference-packet-verified',
          'commit':COMMIT,'observations':observations,'downloaded_files':len(observations),
          'downloaded_bytes':sum(r['bytes'] for r in observations),
          'all_bytes_match_committed_blobs':True,
          'packet_manifest_sha256':sha((OUT/'packet/manifest.json').read_bytes()),
          'source_manifest_sha256':sha((OUT/'packet/source-manifest.json').read_bytes()),
          'evidence_manifest_sha256':sha((OUT/'packet/evidence-manifest.json').read_bytes()),
          'verification':json.loads((OUT/'verification/results.json').read_text()),
          'controls':json.loads((OUT/'controls/results.json').read_text()),
          'fresh_lean_executions':0,'gpu_trials':0,'model_calls':0,
          'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
shutil.copyfile(Path(__file__),OUT/'driver.py')
(OUT/'manifest.json').write_text(json.dumps({p.name:sha(p.read_bytes()) for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps({'status':result['status'],'downloaded_files':result['downloaded_files'],
                  'bytes':result['downloaded_bytes'],'negative_controls':result['controls']['negative_controls']}))
