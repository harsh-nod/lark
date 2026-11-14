"""Download exact-source public FFN bytes anonymously; run only the pinned reader."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import ssl
import subprocess
import sys
import time
import traceback
import urllib.request

BASE=Path(__file__).resolve().parent


def write(name, data):
    p=BASE/(name+'.next')
    p.write_text(json.dumps(data,indent=2)+'\n')
    p.replace(BASE/name)


def sha(p):
    d=hashlib.sha256()
    with p.open('rb') as stream:
        while data:=stream.read(1024*1024):d.update(data)
    return d.hexdigest()


def stage(name, **kwargs):
    write('progress.json',{'pid':os.getpid(),'stage':name,'at_utc':datetime.now(timezone.utc).isoformat(),**kwargs})


def main():
    assert not (BASE/'started.json').exists(), 'Inspect original process; never restart on observation timeout'
    descriptor=json.loads((BASE/'descriptor.json').read_text())
    assert descriptor['source_commit']=='3991812f0170ef73a174eff7be1dcaabb80d46fa'
    assert len(descriptor['files'])==34 and len({r['local'] for r in descriptor['files']})==34
    assert not any((p/'.git').exists() for p in (BASE,*BASE.parents))
    write('started.json',{'pid':os.getpid(),'source_commit':descriptor['source_commit'],
                         'descriptor_sha256':sha(BASE/'descriptor.json')})
    (BASE/'attempts').mkdir()
    context=ssl.create_default_context()
    assert context.check_hostname and context.verify_mode==ssl.CERT_REQUIRED
    opener=urllib.request.build_opener(urllib.request.ProxyHandler({}),urllib.request.HTTPSHandler(context=context))
    downloaded=[]
    for index,row in enumerate(descriptor['files']):
        local=BASE/row['local']
        assert local.is_relative_to(BASE) and '..' not in Path(row['local']).parts
        local.parent.mkdir(parents=True,exist_ok=True)
        url='https://raw.githubusercontent.com/harsh-nod/lark/'+descriptor['source_commit']+'/'+row['path']
        for attempt in range(1,4):
            partial=BASE/'attempts'/f'{index:02d}-{attempt}.part'
            stage('anonymous-download',file=row['path'],url=url,completed_files=len(downloaded),attempt=attempt)
            record={'path':row['path'],'url':url,'attempt':attempt,'authorization_header':False,'tls_verification':True}
            try:
                request=urllib.request.Request(url,headers={'User-Agent':'LARK-FFN-publication-integrity-check'})
                with opener.open(request,timeout=45) as response,partial.open('xb') as target:
                    assert response.status==200 and response.url.startswith('https://raw.githubusercontent.com/')
                    size=0
                    while data:=response.read(1024*1024):
                        target.write(data);size+=len(data)
                        assert size<=row['bytes'], 'Oversized public response'
                    record.update(http_status=response.status,final_url=response.url)
                assert partial.stat().st_size==row['bytes'] and sha(partial)==row['sha256'], 'Public bytes differ'
                partial.rename(local)
                record.update(status='verified',bytes=row['bytes'],sha256=row['sha256'])
                write(f'attempts/{index:02d}-{attempt}.json',record)
                downloaded.append(record)
                write('downloads.json',downloaded)
                break
            except Exception as error:
                record.update(status='failed-attempt-retained',error=repr(error),partial_bytes=partial.stat().st_size if partial.exists() else 0)
                write(f'attempts/{index:02d}-{attempt}.json',record)
                if attempt==3:raise
                time.sleep(0.5)
    reader=BASE/'trusted-reader.py'
    assert sha(reader)==descriptor['reader_sha256']
    assert sha(BASE/'packet/manifest.json')==descriptor['packet_manifest_sha256']
    command=[sys.executable,'-I',str(reader),'--packet',str(BASE/'packet'),
             '--expected-manifest-sha256',descriptor['packet_manifest_sha256'],'--output',str(BASE/'integrity')]
    env=dict(os.environ,PATH='/nonexistent',PYTHONNOUSERSITE='1')
    env.pop('PYTHONPATH',None)
    with (BASE/'reader.stdout').open('xb') as stdout,(BASE/'reader.stderr').open('xb') as stderr:
        child=subprocess.Popen(command,cwd=BASE,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
        stage('independent-pinned-reader',child_pid=child.pid,command=command,downloaded_files=34)
        try:code=child.wait(timeout=120)
        except subprocess.TimeoutExpired:
            os.killpg(child.pid,signal.SIGTERM)
            try:child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid,signal.SIGKILL);child.wait(timeout=5)
            raise
    assert code==0, 'Inspect original reader logs'
    checked=json.loads((BASE/'integrity/results.json').read_text())
    assert checked['archive_members_checked']==4416 and len(checked['archives_checked'])==15
    result={'status':'anonymous-exact-source-FFN-download-and-complete-payload-integrity-passed',
            'source_commit':descriptor['source_commit'],'downloaded_files':34,
            'downloaded_bytes':sum(r['bytes'] for r in downloaded),
            'archives_checked':15,'archive_members_checked':4416,
            'uncompressed_bytes_checked':checked['uncompressed_member_bytes_checked'],
            'all_actual_HTTP200_TLS_anonymous_downloads':True,
            'packet_manifest_sha256':descriptor['packet_manifest_sha256'],'reader_sha256':descriptor['reader_sha256'],
            'captured_code_executed':False,'fresh_Lean_checks':0,'model_calls':0,'GPU_trials':0,
            'new_registered_source_certificates':0,'original_paper_fully_reproduced':False}
    write('results.json',result)
    stage('terminal-success',result=result)
    write('manifest.json',{p.relative_to(BASE).as_posix():sha(p) for p in sorted(BASE.rglob('*')) if p.is_file() and p!=BASE/'manifest.json'})
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    try:main()
    except Exception:
        (BASE/'exception.txt').write_text(traceback.format_exc())
        stage('terminal-failure-inspect-original-state')
        raise
