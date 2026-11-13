"""Package the completed CPU-only assembly study without running an experiment."""

import gzip
import hashlib
import io
import json
from pathlib import Path
import shutil
import tarfile

ROOT = Path('/tmp/lark-full-shape-ptx-compile-packet-v2-20261113')
CURRENT = Path('/tmp/lark-full-shape-ptx-compiled-v2-20261113')
FIRST = Path('/tmp/lark-full-shape-ptx-compiled-v1-20261113')
AUDIT = Path('/tmp/lark-full-shape-ptx-compiled-audit-v1-20261113')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def archive(source, label):
    manifest = read(source/'manifest.json')
    files = {str(p.relative_to(source)):sha(p) for p in source.rglob('*') if p.is_file()}
    require({n:h for n,h in files.items() if n != 'manifest.json'} == manifest,
            'Complete checked recording inventory required')
    write(ROOT/(label+'-files.json'), dict(sorted(files.items())))
    with (ROOT/(label+'.tar.gz')).open('wb') as raw:
        with gzip.GzipFile(fileobj=raw, mode='wb', filename='', mtime=0, compresslevel=9) as zipped:
            with tarfile.open(fileobj=zipped, mode='w') as output:
                for name in sorted(files):
                    data = (source/name).read_bytes()
                    item = tarfile.TarInfo(name)
                    item.size, item.mode, item.mtime = len(data), 0o644, 0
                    output.addfile(item, io.BytesIO(data))
    with tarfile.open(ROOT/(label+'.tar.gz')) as check:
        members = check.getmembers()
        require(len(members) == len(files) and {m.name for m in members} == set(files),
                'Archive file set differs')
        require(all(m.isfile() and hashlib.sha256(check.extractfile(m).read()).hexdigest()
                    == files[m.name] for m in members), 'Archive member hash differs')
    return {'files':len(files), 'uncompressed_bytes':sum((source/n).stat().st_size for n in files),
            'archive_sha256':sha(ROOT/(label+'.tar.gz')),
            'inventory_sha256':sha(ROOT/(label+'-files.json'))}


def main():
    require(not ROOT.exists() and not any((p/'.git').exists() for p in (ROOT,*ROOT.parents)),
            'Fresh packet outside Git required')
    validation = read(AUDIT/'results.json')
    require(validation['status'] == 'full-size-PTX-compilation-recordings-checked'
            and validation['recording_manifest_sha256'] == sha(CURRENT/'manifest.json')
            and validation['first_recording_manifest_sha256'] == sha(FIRST/'manifest.json')
            and validation['PTX_and_cubin_pairs_identical_across_actual_builds'] == 25,
            'Completed independent recording check required')
    ROOT.mkdir(parents=True)
    archives = {label:archive(source,label) for label,source in
                [('raw',CURRENT),('first-build',FIRST),('audit',AUDIT)]}
    for source,name in [(CURRENT/'results.json','raw-results.json'),
                        (FIRST/'results.json','first-build-results.json'),
                        (AUDIT/'results.json','validation.json')]:
        shutil.copyfile(source,ROOT/name)
    result = {
        'schema':1, 'status':'independent-full-size-PTX-assembly-evidence',
        'producer_commit':'86b4861eb7a9c121e84cf0a64c1a550f4069ee6e',
        'initial_producer_commit':'a75d14689a81a4a7920b0a9e846fc35455c12b49',
        'preparation_manifest_sha256':validation['preparation_manifest_sha256'],
        'task_families':17, 'source_stages':25, 'compiled_stages':25, 'assembled_stages':25,
        'reader_refused_stages':25, 'regenerated_reader_probes':25,
        'reader_refusal_codes':validation['reader_refusal_codes'],
        'PTX_and_cubin_pairs_identical_across_actual_builds':25,
        'compiler':'NVIDIA NVRTC 12.9.86', 'assembler':'NVIDIA ptxas 12.9.86',
        'target':'sm_80', 'PTX_version':'8.8', 'unit_tests_passed':3,
        'archives':archives, 'packaging_driver_sha256':sha(Path(__file__)),
        'packaging_model_calls':0, 'packaging_lean_checks':0, 'packaging_gpu_trials':0,
        'new_registered_source_certificates':0, 'original_paper_fully_reproduced':False,
        'nvidia_execution':False,
        'scope':'Compilation/assembly and source/task/recording checks only. No full-size PTX '
                'certificate or model cohort, formal compiler refinement, NVIDIA execution, '
                'numerical equivalence, conformance or timing is claimed. Full source/reference/'
                'task bytes, shapes, dtypes, geometry and fuels are unchanged from the existing '
                'independent CUDA preparation. Fixed-scaffold HIP/CUDA model counts are unchanged. '
                'Both actual CPU compiler recordings are retained; the second adds a closed '
                'compiler/header inventory guard. Identical rebuilds are one set of 25 stages, '
                'not 50 independent kernels.',
    }
    write(ROOT/'results.json', result)
    (ROOT/'packaging-driver.py').write_bytes(Path(__file__).read_bytes())
    (ROOT/'RESULTS.md').write_text('''# Full-size PTX compilation on CPU

All 25 CUDA source stages across the 17 independent full-size benchmark tasks
compiled to PTX 8.8 and assembled for `sm_80` without a GPU. NVRTC and ptxas
were both NVIDIA 12.9.86. The compiler adds only `#include <cuda_fp16.h>`;
original source/reference/task bytes, shapes, dtypes, geometry and fuels are retained.
Fusion contraction and flush-to-zero were disabled; precise division/square-root
options were enabled. These settings do not establish IEEE equivalence.

The existing LARK PTX reader refused all 25 generated programs: three at its
FP32-only type gate and 22 during tokenization. These are first refusals, not
an exhaustive inventory of unsupported features and not counterexamples.
The reader supports a smaller PTX 8.0 scalar subset; broader FP16, control-flow,
instruction and whole-launch proof support still needs implementation.

There are **zero new PTX proofs, model cohorts, source certificates or GPU
trials**. Assembly does not establish the compiler's semantic refinement,
the generated PTX's correctness, NVIDIA execution or hardware conformance.
The existing four tiny PTX certificates and HIP/CUDA model results remain separate.

`raw.tar.gz` retains the complete 346-file recording, exact compiler input,
PTX, cubins, task/reference sources, logs, toolchain/header hashes and reader
refusals. `first-build.tar.gz` retains the earlier 346-file completed build.
The second build closes the compiler/header inventory; all 25 PTX/cubin pairs
match the first build byte-for-byte. These are repeated builds of the same
25 stages, not 50 independent kernels.

The separate `audit.tar.gz` retains source/task/recording checks, 25 regenerated
reader probes and three compiler-boundary tests. It runs no compiler, model,
Lean or GPU experiment and executes no captured Python. All archive members
and the top-level packet are hash bound. The original paper is not fully reproduced.
''')
    write(ROOT/'manifest.json', {p.name:sha(p) for p in sorted(ROOT.iterdir()) if p.is_file()})
    print(json.dumps({'output':str(ROOT),'files':len(list(ROOT.iterdir())),
                      'bytes':sum(p.stat().st_size for p in ROOT.iterdir()),
                      'manifest_sha256':sha(ROOT/'manifest.json'),'archives':archives}))


if __name__ == '__main__':
    main()
