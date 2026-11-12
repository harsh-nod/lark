from pathlib import Path
import hashlib,json,os,re,shutil,subprocess,time
import lark_kernels
from lark_kernels import native_sglang_rmsnorm_certificate as native
out=Path("/tmp/lark-sglang-installed-wheel-check-v23-v1-20261112")
out.mkdir(exist_ok=False)
repo=Path("/tmp/lark-native-sglang-rmsnorm-20261112")
case=repo/"reproduction/production_sglang_rmsnorm/cases/native_fixed"
venv=Path("/tmp/lark-sglang-installed-v23-v1-20261112")
assert not any((p/".git").exists() for p in (out,*out.parents))
assert str(venv) in lark_kernels.__file__
assert len(native.libraries())==88
resources=json.loads(Path("/tmp/lark-sglang-wheel-resources-v23-v1-20261112.json").read_text())
for relative,expected in resources["proof_resources"].items():
 name=relative.removeprefix("lean-real/").removeprefix("lean/")
 assert hashlib.sha256(native.libraries()[name]).hexdigest()==expected
checks=[]
env=dict(os.environ)
env["LARK_REAL_PROJECT"]="/tmp/lark-native-qknorm-rope-20261111/lean-real"
env["PYTHONNOUSERSITE"]="1"
env.pop("PYTHONPATH",None)
env.pop("LEAN_PATH",None)
commands=[("verify",[str(venv/"bin/lark"),"verify-native-sglang-rmsnorm",str(case/"kernel.hip"),"--reference",str(case/"reference.py"),"--task",str(case/"task.json"),"--output",str(out/"certificate"),"--lean","/tmp/lean-4.19.0-linux/bin/lean","--timeout","600"]),
 ("recheck",[str(venv/"bin/lark"),"check",str(out/"certificate"),"--lean","/tmp/lean-4.19.0-linux/bin/lean","--timeout","600"])]
for name,command in commands:
 before=time.monotonic()
 r=subprocess.run(command,cwd=out,env=env,text=True,capture_output=True,timeout=650)
 (out/(name+".log")).write_text(r.stdout+r.stderr)
 assert r.returncode==0,(name,r.returncode)
 checks.append({"name":name,"exit_code":r.returncode,"seconds":time.monotonic()-before,"timed_out":False})
report=json.loads((out/"certificate/report.json").read_text())
assert report["status"]=="verified" and report["whole_launch_proved"] is True
assert report["source_reference_equality_proved"] is True
assert report["model_profile"]==native.PROFILE
assert "sorryAx" not in report["axiom_audit"]
assert len(re.findall(r"'LarkCertificate\.",report["axiom_audit"]))==8
result={"schema":1,"status":"installed-wheel-native-sglang-real-certificate-verified-and-rechecked-outside-checkout",**resources,
 "package_path":lark_kernels.__file__,"model_profile":native.PROFILE,"local_lean_modules":88,"source_certificates":1,
 "source_reference_equality_proved":True,"whole_kernel_execution_proved":True,"actual_trace_race_freedom_proved":True,
 "source_checked_managed_library_cache_reused":True,"installed_verification_outside_checkout":True,
 "ieee_equivalence_proved":False,"floating_point_error_bound_proved":False,"original_paper_fully_reproduced":False,
 "model_calls":0,"gpu_trials":0,"checks":checks}
(out/"results.json").write_text(json.dumps(result,indent=2)+"\n")
for src,name in [(Path("/tmp/lark-sglang-wheel-build-v23-v3-20261112.log"),"wheel-build.log"),(Path("/tmp/lark-sglang-wheel-install-v23-v1-20261112.log"),"wheel-install.log"),(Path(__file__),"checker.py")]:
 shutil.copyfile(src,out/name)
(out/"manifest.json").write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.is_file()},indent=2)+"\n")
print(json.dumps({k:result[k] for k in ("status","local_lean_modules","source_certificates")}))
