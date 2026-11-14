"""Promote only the exact fully checked public v27 commit, with no force push."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess

ROOT=Path('/home/harsh/lark')
OUT=Path('/tmp/lark-v27-main-promotion-v2-20261114')
SOURCE='0911ad6ec09aea6bc9dd37ae4526165a531e62c1'
OLD='a869373b20b15c1050303886ce5c62e970deea81'
RUN=43587053488
PUBLIC=Path('/tmp/lark-v27-anonymous-publication-return-v7-20261114/verified')
OBS=Path('/tmp/lark-paper-v27-source-ci-v10-20261114')
GIT=['git','-c','http.proxy=socks5h://127.0.0.1:19089','-c','http.postBuffer=536870912','-c','http.version=HTTP/1.1']
ENV=dict(os.environ,HTTPS_PROXY='socks5://127.0.0.1:19089')


def read(p):return json.loads(p.read_text())
def write(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()


def api(resource,label):
    r=subprocess.run(['gh','api','repos/harsh-nod/lark'+('/'+resource if resource else '')],env=ENV,capture_output=True,timeout=40)
    (OUT/(label+'.json')).write_bytes(r.stdout)
    (OUT/(label+'.stderr')).write_bytes(r.stderr)
    assert r.returncode==0,r.stderr
    return json.loads(r.stdout)


def main():
    assert not OUT.exists(), 'Inspect actual original promotion state instead of restarting'
    OUT.mkdir()
    (OUT/'promotion-driver.py').write_bytes(Path(__file__).read_bytes())
    assert git('rev-parse','HEAD')==OLD and git('branch','--show-current')=='main'
    assert not git('status','--porcelain')
    subprocess.run(['git','merge-base','--is-ancestor',OLD,SOURCE],cwd=ROOT,check=True)
    repository=api('','repository')
    assert repository['private'] is False and repository['visibility']=='public'
    run=api(f'actions/runs/{RUN}','source-run')
    response=api(f'actions/runs/{RUN}/jobs?per_page=100','source-jobs')
    summary=read(OBS/'results.json')
    assert run['id']==RUN and run['head_sha']==SOURCE and run['status']=='completed' and run['conclusion']=='success'
    assert run['head_branch']=='reproduction/paper-v27' and run['event']=='push' and run['run_attempt']==1
    assert response['total_count']==len(response['jobs'])==24
    assert len({j['id']for j in response['jobs']})==24
    assert {j['name']for j in response['jobs']}==set(summary['expected_jobs'])
    assert all(j['status']=='completed' and j['conclusion']=='success' and j['run_id']==RUN and j['head_sha']==SOURCE for j in response['jobs'])
    assert summary['source_commit']==SOURCE and summary['successful_jobs']==24 and summary['status']=='exact-source-CI-all-24-passed'
    assert summary['observer_sha256']==sha(OBS/'observer.py')
    capture=read(PUBLIC/'capture.json')
    publication=read(PUBLIC/'observer/results.json')
    actual=read(PUBLIC/'public/results.json')
    controls=read(PUBLIC/'public/validation/results.json')
    descriptor=read(PUBLIC/'observer/descriptor.json')
    assert publication['source_commit']==actual['source_commit']==descriptor['source_commit']==SOURCE
    assert publication['status']=='anonymous20-file-source-exact-v27-download-and-all98-controls-passed'
    assert capture['all20_downloaded_files_rehashed_on_capture'] is True
    assert capture['all98_control_logs_returned'] is True and capture['publication_or_control_reruns']==0
    assert actual['authenticated_download_requests'] is False and actual['tls_verification'] is True
    assert actual['all_downloads_match_committed_bytes'] is True and len(actual['downloaded_files'])==20
    assert publication['downloaded_bytes']==actual['total_downloaded_bytes']==descriptor['bytes']==485439169
    assert controls['checks']==descriptor['expected_98_check_records'] and len(controls['checks'])==98
    assert controls['positive_replays']==9 and controls['negative_controls']==89
    assert controls['all_control_payloads_complete_during_replay'] is True
    assert len(list((PUBLIC/'public/validation').glob('*.log')))==98
    for row in actual['downloaded_files']:
        assert row['http_status']==200 and row['tls_verification'] is True and row['authorization_header'] is False
    for name,expected in [('20261113-v26','251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed'),
                          ('20261113-v27','aa23c786cf8a7c2ca059c76beddcb86dc148dc03e3d70096e0bd2f930044fea0')]:
        path='reproduction/paper_results/snapshots/'+name+'/manifest.json'
        assert hashlib.sha256(subprocess.check_output(['git','show',SOURCE+':'+path],cwd=ROOT)).hexdigest()==expected
    base='reproduction/paper_results/snapshots/20261113-v26'
    assert git('rev-parse',OLD+':'+base)==git('rev-parse',SOURCE+':'+base)
    replayer=subprocess.check_output(['git','show',SOURCE+':reproduction/paper_results/replay_snapshot.py'],cwd=ROOT)
    assert b'DEFAULT = Path(__file__).resolve().parent / "snapshots/20261113-v27"'in replayer
    config=json.loads(subprocess.check_output(['git','show',SOURCE+':reproduction/paper_results/snapshots/20261113-v27/targets.json'],cwd=ROOT))
    assert 'ptx_rotary_proof'in config and 'ptx_ffn_proof'not in config
    before=subprocess.check_output([*GIT,'ls-remote','origin','refs/heads/main'],cwd=ROOT,text=True,timeout=40).split()[0]
    assert before==OLD
    write(OUT/'preflight.json',{'status':'all-required-exact-source-CI-and-anonymous-full98-publication-gates-passed',
          'old_main':OLD,'target':SOURCE,'CI_run':RUN,'CI_jobs':24,'anonymous_files':20,
          'positive_replays':9,'negative_controls':89,'frozen_v26_unchanged':True,'force':False})
    command=[*GIT,'push','origin',SOURCE+':refs/heads/main']
    with(OUT/'push.stdout').open('xb')as stdout,(OUT/'push.stderr').open('xb')as stderr:
        child=subprocess.Popen(command,cwd=ROOT,stdout=stdout,stderr=stderr)
        write(OUT/'progress.json',{'pid':os.getpid(),'child_pid':child.pid,'stage':'normal-main-fast-forward',
                                 'old_main':OLD,'target':SOURCE,'command':command})
        code=child.wait()
    assert code==0, 'Inspect actual push output and remote ref; never repeat a live promotion'
    remote=subprocess.check_output([*GIT,'ls-remote','origin','refs/heads/main'],cwd=ROOT,text=True,timeout=40).split()[0]
    assert remote==SOURCE
    write(OUT/'remote-update.json',{'status':'actual-remote-main-verified','old_main':OLD,'new_main':SOURCE,'force':False})
    assert git('rev-parse','HEAD')==OLD and not git('status','--porcelain')
    subprocess.run(['git','-c','gc.auto=0','merge','--ff-only','--quiet',SOURCE],cwd=ROOT,check=True)
    assert git('rev-parse','HEAD')==SOURCE and not git('status','--porcelain')
    result={'status':'six-family-v27-main-exact-tested-nonforce-fast-forward-verified',
            'old_main':OLD,'promoted_commit':SOURCE,'source_CI_commit':SOURCE,'CI_run':RUN,'successful_CI_jobs':24,
            'promoted_commit_is_exact_CI_checked_commit':True,'public_main_verified':True,'local_main_verified':True,
            'force':False,'anonymous_downloaded_files':20,'full_ledger_checks':98,'frozen_v26_unchanged':True,
            'FFN_separate_draft_source':'3991812f0170ef73a174eff7be1dcaabb80d46fa',
            'direct_new_Lean_checks':0,'direct_model_calls':0,'direct_GPU_trials':0,
            'manual_CI_reruns':0,'GitHub_may_automatically_start_its_main_push_workflow':True,
            'original_paper_fully_reproduced':False,'at_utc':datetime.now(timezone.utc).isoformat()}
    write(OUT/'results.json',result)
    write(OUT/'manifest.json',{p.name:sha(p)for p in sorted(OUT.iterdir())if p.is_file()and p.name!='manifest.json'})
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
