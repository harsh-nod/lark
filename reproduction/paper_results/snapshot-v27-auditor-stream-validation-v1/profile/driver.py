"""Profile the complete unchanged ledger with the new authored stream buffer."""
import cProfile
import hashlib
import io
import json
import os
from pathlib import Path
import pstats
import shutil
import subprocess
import sys
import time
import traceback

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-v27-auditor-buffer-profile-v1-20261114')


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    OUT.mkdir(exist_ok=False)
    (OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
    isolated=OUT/'isolated';helpers=isolated/'bin';helpers.mkdir(parents=True)
    for name in ['replay_snapshot.py','snapshot_archives.py']:
        shutil.copy2(ROOT/'reproduction/paper_results'/name,helpers/name)
    snapshot=isolated/'snapshot'
    shutil.copytree(ROOT/'reproduction/paper_results/snapshots/20261113-v27',snapshot,copy_function=os.link)
    assert sha(snapshot/'manifest.json')=='aa23c786cf8a7c2ca059c76beddcb86dc148dc03e3d70096e0bd2f930044fea0'
    paper=isolated/'paper-source.tar';os.link('/tmp/lark-reproduction-paper-source.tar',paper)
    assert sha(paper)=='095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    for key in ['PYTHONPATH','LEAN_PATH']:os.environ.pop(key,None)
    os.environ.update(PATH='/nonexistent',PYTHONNOUSERSITE='1')
    os.chdir(isolated);sys.path.insert(0,str(helpers))
    import replay_snapshot
    actual_run=subprocess.run;commands=[]
    def traced(command,*args,**kwargs):
        if len(command)>3 and command[1]=='-I' and command[3]=='--_frozen-auditor':
            profiled=[command[0],'-I','-m','cProfile','-o',str(OUT/'auditor.prof'),*command[2:]]
            commands.append({'original':command,'profiled':profiled,'timeout_seconds':kwargs.get('timeout')})
            return actual_run(profiled,*args,**kwargs)
        return actual_run(command,*args,**kwargs)
    subprocess.run=traced
    began=time.monotonic();profile=cProfile.Profile();code=0
    try:
        profile.runcall(replay_snapshot.replay,snapshot,paper)
    except BaseException:
        code=1;(OUT/'exception.txt').write_text(traceback.format_exc())
    finally:
        profile.dump_stats(str(OUT/'replay.prof'))
        for name in ['replay','auditor']:
            if (OUT/(name+'.prof')).exists():
                output=io.StringIO();pstats.Stats(str(OUT/(name+'.prof')),stream=output).sort_stats('cumulative').print_stats(65)
                (OUT/(name+'-stats.txt')).write_text(output.getvalue())
    result={'status':'complete-profiled-ledger-replay-passed' if code==0 else 'profiled-replay-failed',
        'seconds_including_profile_overhead':time.monotonic()-began,'commands':commands,
        'all_snapshot_bytes_unchanged':True,'snapshot_manifest_sha256':sha(snapshot/'manifest.json'),
        'executed_helpers':{p.name:sha(p) for p in helpers.iterdir() if p.is_file()},
        'fresh_Lean_GPU_model_experiments':0,'new_full98_control_suite_claim':False,
        'original_paper_fully_reproduced':False}
    assert len(commands)==1
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'manifest.json').write_text(json.dumps({p.relative_to(OUT).as_posix():sha(p) for p in sorted(OUT.rglob('*'))
        if p.is_file() and 'snapshot' not in p.relative_to(OUT).parts and p.name!='paper-source.tar'},indent=2)+'\n')
    print(json.dumps(result),flush=True)
    raise SystemExit(code)


if __name__=='__main__':main()
