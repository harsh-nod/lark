ROOT='/tmp/lark-full-shape-models-20261112'
OUT='/tmp/lark-proof-parser-wheel-validation-v2-20261112'
from pathlib import Path
import json,hashlib
from lark_kernels.proof_syntax import source_path,check_terms
from lark_kernels import certificate
root=Path(ROOT);out=Path(OUT)
assert source_path().is_relative_to(out/'venv')
assert source_path().read_bytes()==(root/'lean/Lark/ProofSyntax.lean').read_bytes()
lean='/tmp/lean-4.19.0-linux/bin/lean'
a,alog=check_terms({'proof':'by rfl'},lean,180)
b,blog=check_terms({'proof':'by rfl\nopen Nat'},lean,180)
assert a and not b
(out/'positive-syntax.log').write_text(alog);(out/'negative-syntax.log').write_text(blog)
case=root/'reproduction/cases/relu'
r=certificate.verify(case/'kernel.hip',case/'reference.py',case/'task.json',out/'certificate',lean=lean,timeout=180)
assert r['status']=='verified'
certificate.check(out/'certificate',lean=lean,timeout=180)
print(json.dumps({'status':'installed-wheel-parser-and-certificate-passed','outside_checkout':True,'parser_source':str(source_path()),'parser_source_sha256':hashlib.sha256(source_path().read_bytes()).hexdigest(),'test_certificate_exports':1,'model_calls':0,'gpu_trials':0,'paper_result_certificates':0,'original_paper_fully_reproduced':False}))
