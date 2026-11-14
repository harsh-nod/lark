from pathlib import Path
import json,sys,sysconfig
from lark_kernels import ptx_ffn_certificate as checker
from lark_kernels import pointwise
venv,recording = map(Path,sys.argv[1:])
package=Path(checker.__file__).resolve()
library=pointwise.induction_path().resolve()
assert package.is_relative_to(venv.resolve()), str(package)
assert library.is_relative_to(venv.resolve()), str(library)
assert str(library).endswith('/share/lark/lean/Lark/Pointwise.lean')
expected=checker.read(recording/'source-bindings.json')
actual={n:checker.sha(v) for n,v in checker.own_sources().items()}
assert actual==expected
print(json.dumps({'installed_checker':str(package),'installed_Lean_library':str(library),
'owned_source_bindings_checked':len(actual),'all_owned_bytes_equal_to_export':True,
'isolated_python':bool(sys.flags.isolated),'data_path':sysconfig.get_path('data')}))
