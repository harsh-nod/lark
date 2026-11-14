"""Cold-check the independent full-size FFN reference, not a kernel certificate."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import signal
import subprocess
import sys
import time

ROOT=Path('/tmp/lark-ptx-ffn-refinement-20261114')
OUT=Path('/tmp/lark-ptx-ffn-reference-check-v13-20261114')
LEAN=Path('/tmp/lean-4.19.0-linux/bin/lean')
sys.path.insert(0,str(ROOT))
from lark_kernels import ptx_ffn, ptx_pointwise_certificate as common


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def write(name,value):(OUT/name).write_text(json.dumps(value,indent=2)+'\n')


def main():
    OUT.mkdir(exist_ok=False)
    (OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
    assert sha(LEAN)==common.LEAN_SHA256
    source=OUT/'source';(source/'Lark').mkdir(parents=True)
    inputs=ROOT/'reproduction/ptx/full-size/ffn'
    shutil.copytree(inputs,OUT/'inputs')
    tasks,parsed,body=ptx_ffn.prepare(*[(inputs/s/'kernel.ptx').read_text() for s in ('up','down')],
        (inputs/'reference.py').read_text(),*[(inputs/s/'task.json').read_text() for s in ('up','down')])
    for name in ['Nonlinear','PtxFeedForwardReference']:
        shutil.copy2(ROOT/'lean/Lark'/(name+'.lean'),source/'Lark'/(name+'.lean'))
    shutil.copytree(ROOT/'lark_kernels',OUT/'tool-sources',ignore=shutil.ignore_patterns('__pycache__'))
    rendered=ptx_ffn.lean_reference(body)
    (source/'Main.lean').write_text('''import Lark.PtxFeedForwardReference
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace LarkCompiledFfnReferenceInput
open LarkNonlinear LarkPtxFeedForward.Reference
def body : TensorReference := '''+rendered+'''
theorem reference_body : body = referenceBody := by rfl
theorem reference_denotation (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ht : t < 16384) :
    (match evaluate ops input body with
     | some tensor => tensor.cell t
     | none => none) = some (outputValue ops input t) := by
  rw [reference_body, evaluate_body]
  exact reference_cell ops input t ht
#print axioms reference_body
#print axioms reference_denotation
end LarkCompiledFfnReferenceInput
''')
    write('prepared-inputs.json',{'instructions':[len(t.instructions) for t in parsed],
        'grid':[t.grid for t in tasks],'fuel':[list(t.fuel) for t in tasks],
        'reference_body':body,'scope':'Independent tensor denotation only; no compiled-kernel correctness claim.'})
    env=dict(os.environ,LEAN_PATH=str(source),PYTHONNOUSERSITE='1')
    env.pop('PYTHONPATH',None)
    started=time.monotonic();checks=[];audits={};code=0
    for name in ['Nonlinear','PtxFeedForwardReference','Main']:
        relative='Main.lean' if name=='Main' else 'Lark/'+name+'.lean'
        command=[str(LEAN),'-o',relative.removesuffix('.lean')+'.olean',relative]
        limit=min(180,600-(time.monotonic()-started));assert limit>0
        begin=time.monotonic();timed_out=False
        with (OUT/(name+'.log')).open('wb') as output:
            child=subprocess.Popen(command,cwd=source,env=env,stdout=output,stderr=subprocess.STDOUT,start_new_session=True)
            write('progress.json',{'pid':os.getpid(),'child_pid':child.pid,'stage':name,'command':command})
            try:code=child.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                timed_out=True;os.killpg(child.pid,signal.SIGKILL);code=child.wait(timeout=5)
        checks.append({'module':name,'command':command,'exit_code':code,'timed_out':timed_out,'seconds':time.monotonic()-begin})
        if code or timed_out:break
        prefix={'Nonlinear':'LarkNonlinear','PtxFeedForwardReference':'LarkPtxFeedForward.Reference','Main':'LarkCompiledFfnReferenceInput'}[name]
        tags=[n if '.' in n else prefix+'.'+n for n in re.findall(r'^#print axioms (\S+)',(source/relative).read_text(),re.M)]
        audits.update(common.audits((OUT/(name+'.log')).read_text(),tags))
    result={'status':'independent-full-size-FFN-reference-denotation-passed' if code==0 and len(checks)==3 else 'failed-reference-development-check',
        'observed_at_utc':datetime.now(timezone.utc).isoformat(),'module_checks':checks,'axiom_audits':audits,
        'total_seconds':time.monotonic()-started,'Lean_sha256':sha(LEAN),'original_stack_limits':resource.getrlimit(resource.RLIMIT_STACK),
        'limits':common.LIMITS,'all_own_modules_fresh':True,'source_import_build_seconds':600,
        'compiled_FFN_kernel_correctness_proofs':0,'new_registered_source_certificates':0,
        'GPU_trials':0,'model_calls':0,'original_paper_fully_reproduced':False}
    write('results.json',result)
    write('manifest.json',{p.relative_to(OUT).as_posix():sha(p) for p in sorted(OUT.rglob('*')) if p.is_file()})
    print(json.dumps(result),flush=True)
    raise SystemExit(0 if result['status'].endswith('-passed') else 1)


if __name__=='__main__':main()
