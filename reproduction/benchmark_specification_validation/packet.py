"""Versioned, source-bound audit packet for the full CPU benchmark-reference study.

Verification checks artifact integrity, scope and recorded numerical consistency.
The replay subcommand executes the frozen sources to verify the computations.
"""
import argparse
import gzip
import hashlib
import importlib.util
import io
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import struct
import subprocess
import sys
import tarfile
import tempfile

SOURCE_CHECKPOINT = 'f7c0ecc0c416786337e72a90bb43a4bba348cc57'
SOURCE_BINDINGS_SHA256 = 'e635d0ee3517069b62d49f9d59c9fd49f022953df8c64d758e745b3795697da8'
SOURCE_FILE_COUNT = 145
HERE = 'reproduction/benchmark_specification_validation/'
METHOD = 'actual-polymorphic-reference-checked-float64'
STRATA = ['dyadic','normal','basis','cancellation']
MODELS = {
    'relu':'LarkPointwise.spec', 'silu':'LarkPointwise.spec', 'gelu':'LarkPointwise.spec',
    'rmsnorm':'LarkUnaryMap.spec','layernorm':'LarkUnaryMap.spec','softmax':'LarkUnaryMap.spec',
    'gemv':'LarkReduction.matrixSpec','gemm':'LarkDot.matrixSpec','bmm':'LarkDot.matrixSpec',
    'linear':'LarkBias.matrixSpec','conv2d':'LarkDot.matrixSpec','depthwise_conv':'LarkDot.matrixSpec',
    'rope':'LarkRotary.spec','ffn':'LarkPipeline.spec','swiglu':'LarkSwiGLU.spec',
    'attention':'LarkAttention.spec','gqa':'LarkAttention.spec',
}
MODULES = ('BenchmarkRealAudit.lean','BenchmarkRealAudit.olean',
           'BenchmarkFloatAudit.lean','BenchmarkFloatAudit.olean')
FALSE_FLAGS = ('original_paper_fully_reproduced','ieee_equivalence_theorem',
               'floating_point_error_bound')

def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text(),parse_constant=lambda token: (_ for _ in ()).throw(ValueError('Nonfinite JSON constant: '+token)))


def write(path, value):
    path.write_text(json.dumps(value,indent=2)+'\n')


def safe(name):
    path = PurePosixPath(name)
    require(bool(path.parts) and not path.is_absolute() and '..' not in path.parts
            and str(path) == name, 'Unsafe packet path')
    return path


def verify_files(root, manifest):
    require(type(manifest) is dict and bool(manifest), 'Empty file manifest')
    for name, expected in manifest.items():
        path = root/safe(name)
        require(path.is_file() and not path.is_symlink() and sha(path) == expected,
                'File hash/path differs: '+name)


def pack(destination, root, names):
    manifest = {}
    with destination.open('wb') as raw:
        with gzip.GzipFile(fileobj=raw,mode='wb',filename='',mtime=0) as compressed:
            with tarfile.open(fileobj=compressed,mode='w') as archive:
                for name in sorted(names):
                    path = root/safe(name)
                    require(path.is_file() and not path.is_symlink(), 'Nonregular source/evidence')
                    blob = path.read_bytes()
                    entry = tarfile.TarInfo(name)
                    entry.size, entry.mode, entry.mtime = len(blob), 0o644, 0
                    archive.addfile(entry, io.BytesIO(blob))
                    manifest[name] = hashlib.sha256(blob).hexdigest()
    return manifest


def unpack(archive, destination, manifest):
    destination.mkdir(parents=True,exist_ok=False)
    seen, total = set(), 0
    with tarfile.open(archive) as stream:
        for entry in stream:
            name = safe(entry.name)
            require(entry.isfile() and entry.name in manifest and entry.name not in seen
                    and entry.size <= 128_000_000 and not any(p in ('.git','.lake') for p in name.parts)
                    and not entry.name.endswith(('.olean','.ilean','.so','.pyc')), 'Unexpected archive entry')
            total += entry.size
            require(total <= 1_000_000_000, 'Archive exceeds evidence/source bound')
            blob = stream.extractfile(entry).read()
            require(hashlib.sha256(blob).hexdigest() == manifest[entry.name], 'Archived bytes differ')
            path = destination/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(blob)
            seen.add(entry.name)
    require(seen == set(manifest), 'Incomplete archive')


def finite(value):
    return type(value) in (int,float) and math.isfinite(value)


def digest(value):
    return type(value) is str and re.fullmatch('[0-9a-f]{64}',value) is not None


def bits(value):
    require(type(value) is str and value.isdecimal() and str(int(value)) == value
            and 0 <= int(value) < 2**64, 'Invalid Float64 bit string')
    number = struct.unpack('<d',struct.pack('<Q',int(value)))[0]
    require(math.isfinite(number),'Nonfinite Float64 payload')
    return number


def caps(text):
    found = re.findall(r'^\s*set_option\s+(maxRecDepth|maxHeartbeats)\s+(\S+)',text,re.M)
    require(found == [('maxRecDepth','10000'),('maxHeartbeats','2000000')],
            'Changed or duplicated numerical resource limits')


def records(path, marker='LARK_SPEC_AUDIT '):
    text = path.read_text()
    require(not any(token in text for token in ('PANIC','stacktrace:','Stack overflow','sorryAx')),
            'Panic or invalid proof log')
    return [json.loads(line.split(marker,1)[1]) for line in text.splitlines() if marker in line]


def load_source_study(source):
    # Only load code after all 145 files match the immutable protocol pin.
    sys.dont_write_bytecode = True
    for name in list(sys.modules):
        if name == 'lark_kernels' or name.startswith('lark_kernels.'):
            del sys.modules[name]
    sys.path.insert(0,str(source))
    specification = importlib.util.spec_from_file_location('_frozen_benchmark_study',source/HERE/'study.py')
    module = importlib.util.module_from_spec(specification)
    sys.modules[specification.name] = module
    specification.loader.exec_module(module)
    return module


VALIDATED_INPUTS = set()


def inputs(path, metadata):
    signature = (sha(path),json.dumps(metadata,sort_keys=True))
    if signature in VALIDATED_INPUTS:
        return
    data = read(path)
    require(set(data) == {'schema','buffers'} and type(data['schema']) is int and data['schema'] == 1,
            'Changed numerical input schema')
    require(type(data['buffers']) is list and len(data['buffers']) == len(metadata['buffers']),
            'Input buffer arity differs')
    for values, definition in zip(data['buffers'],metadata['buffers']):
        count = math.prod(definition['shape']) if definition['role'] != 'output' else 0
        require(type(values) is list and len(values) == count, 'Input buffer shape differs')
        encoding = {'float16':'<e','float32':'<f','float64':'<d'}[definition['dtype']]
        for value in values:
            number = bits(value)
            rounded = struct.unpack(encoding,struct.pack(encoding,number))[0]
            require(struct.pack('<d',rounded) == struct.pack('<d',number),
                    'Input is not quantized to its declared storage dtype')
    VALIDATED_INPUTS.add(signature)


NUMERICAL_NAMES = ('positive','semantic-doubling','wrong-type','output-index','input-buffer',
    'input-offset','zero-literal-denominator','zero-division-denominator','negative-sqrt',
    'nonfinite-input','nonfinite-intermediate','unknown-input-schema','duplicate-output',
    'empty-output','unsupported-float-operation','unregistered-helper','unsafe-reference',
    'injected-entrypoint')
NUMERICAL_REFUSALS = dict(zip(NUMERICAL_NAMES[2:], (
    'reference-audit expected polymorphic Ops reference',
    'reference-audit output index out of bounds',
    'reference-audit input index out of bounds','reference-audit input index out of bounds',
    'reference-audit zero denominator','reference-audit zero denominator',
    'reference-audit negative square-root input','reference-audit non-finite input',
    'reference-audit non-finite intermediate','reference-audit unknown input schema',
    'reference-audit duplicate output index','reference-audit empty output selection',
    'reference-audit unsupported declaration: Float.exp',
    'reference-audit unsupported declaration owner: Unregistered.number',
    'reference-audit unsafe declaration: LarkCertificate.spec',
    'reference-audit unsupported reference entrypoint')))
CACHE_NAMES = ('signed-zero','cache-index','empty-cache','nonfinite-cache','callback-error',
               'different-ops','different-shape-expression','different-input-expression')
CACHE_REFUSALS = dict(zip(CACHE_NAMES[1:], (
    'reference-audit materialized score index out of bounds',
    'reference-audit materialized score index out of bounds',
    'reference-audit non-finite intermediate','reference-audit injected score failure',
    *(['reference-audit unsupported score call for materialization']*3))))


def audit_controls(source, evidence, report):
    for category, names, script, status in [
        ('numerical',NUMERICAL_NAMES,'controls.py','compiled-numerical-auditor-controls-passed'),
        ('materialization',CACHE_NAMES,'materialization_controls.py','materialization-controls-passed')]:
        directory = evidence/(category+'-controls')
        data = read(directory/'results.json')
        receipt = report['controls'][category]
        require(set(receipt) == {'status','positive_controls','negative_controls','report_sha256',
                                'driver_log_sha256'},'Control receipt schema differs')
        require(data['status'] == receipt['status'] == status and
                data['positive_controls'] == receipt['positive_controls'] == 1 and
                data['negative_controls'] == receipt['negative_controls'] == len(names)-1,
                'Control counts/status differ')
        require(data['module_bindings'] == report['module_bindings'] and
                data['driver_sha256'] == sha(source/HERE/script), 'Control sources differ')
        require(data['new_certificates'] == 0 and data['original_paper_fully_reproduced'] is False,
                'Control scope inflated')
        require(receipt['report_sha256'] == sha(directory/'results.json') and
                receipt['driver_log_sha256'] == sha(evidence/(category+'-controls-driver.log')),
                'Control receipt hash differs')
        require([row['control'] for row in data['controls']] == list(names),'Control roster differs')
        for row in data['controls']:
            name = row['control']; folder = directory/name
            require(finite(row['seconds']) and 0 <= row['seconds'] <= 180,'Control time exceeds limit')
            require(row['main_sha256'] == sha(folder/'Main.lean') and
                    row['log_sha256'] == sha(folder/'lean.log'),'Control file hash differs')
            caps((folder/'Main.lean').read_text())
            log = (folder/'lean.log').read_text()
            parsed = records(folder/'lean.log')
            if category == 'numerical':
                require(row['input_sha256'] == sha(folder/'Input.json'),'Control input hash differs')
                if name in ('positive','semantic-doubling'):
                    value = 1.25 if name == 'positive' else 2.5
                    require(row['exit_code'] == 0 and len(parsed) == 1 and
                            bits(parsed[0]['float64_bits']) == row['lean_float64'] == value and
                            row['independent_expected'] == 1.25 and
                            row['outcome'] == ('matched' if name == 'positive'
                                               else 'numerical-mismatch-detected'),
                            'Positive/semantic control differs')
                else:
                    require(row['exit_code'] != 0 and row['outcome'] == 'refused' and not parsed and
                            row['expected_refusal'] == NUMERICAL_REFUSALS[name] and
                            NUMERICAL_REFUSALS[name] in log,'Numerical refusal differs')
            elif name == 'signed-zero':
                require(row['exit_code'] == 0 and row['outcome'] == 'bit-identical' and
                        'LARK_CACHE_CONTROL 9223372036854775808' in log,'Signed-zero cache changed')
            else:
                require(row['exit_code'] != 0 and row['outcome'] == 'refused' and
                        'LARK_CACHE_CONTROL' not in log and CACHE_REFUSALS[name] in log,
                        'Cache refusal differs')


SAMPLE_KEYS = {'absolute_error','compiled_float64_scalar','elaborated_real_expression',
    'elaborated_real_scalar','elaborated_real_type','evaluation_strategy','float64_bits','index',
    'lean_float64','method','original_dtype_finite','output_count','source_float64_scalar',
    'torch_ideal_float64','torch_original_dtype','validated_declarations',
    'validated_reference_declarations'}
REPORT_KEYS = {'absolute_tolerance','checks','controls','driver_sha256','floating_point_error_bound',
    'gpu_trials','ieee_equivalence_theorem','import_bindings','maxHeartbeats','maxRecDepth',
    'max_absolute_error','method','model_calls','module_bindings','new_certificates',
    'original_paper_fully_reproduced','per_process_timeout_seconds','platform','python',
    'relative_tolerance','sample_count','schema','score_comparison_count','seed','selected_cases',
    'source_bindings_sha256','source_file_count','status','storage_conversions','strata','torch_version'}
CASE_KEYS = {'case','stratum','samples','seconds','input_metadata','case_source_bindings',
             'main_sha256','input_sha256','log_sha256'}


def audit_sample(row, logged, index, count, key, strategy):
    require(set(row) == SAMPLE_KEYS and type(row['index']) is int and row['index'] == index
            and row['output_count'] == count and row['method'] == METHOD and
            row['evaluation_strategy'] == strategy,'Sample scope differs')
    added = {'absolute_error','lean_float64','original_dtype_finite',
             'torch_ideal_float64','torch_original_dtype'}
    require({name:value for name,value in row.items() if name not in added} == logged,
            'Sample differs from Lean log')
    value = bits(row['float64_bits']); expected = row['torch_ideal_float64']
    require(finite(expected) and finite(row['lean_float64']) and finite(row['absolute_error']) and
            value == row['lean_float64'] and abs(value-expected) == row['absolute_error'] and
            abs(value-expected) <= 1e-10+1e-10*abs(expected),'Numerical comparison differs')
    require(type(row['original_dtype_finite']) is bool and
            (finite(row['torch_original_dtype']) if row['original_dtype_finite']
             else row['torch_original_dtype'] is None),'Actual-dtype scope differs')
    require(row['elaborated_real_type'] == 'List ℝ' and
            row['elaborated_real_expression'] == 'spec LarkReal.ops LarkBenchmarkRealAudit.input',
            'Elaborated real-reference scope differs')
    require(type(row['elaborated_real_scalar']) is str and
            'LarkReal.ops' in row['elaborated_real_scalar'] and
            'LarkBenchmarkRealAudit.input' in row['elaborated_real_scalar'],
            'Elaborated real scalar differs')
    for field in ('validated_reference_declarations','validated_declarations'):
        require(type(row[field]) is list and bool(row[field]) and
                len(set(row[field])) == len(row[field]) and
                all(type(name) is str and name for name in row[field]),'Declaration receipt differs')
    require('LarkCertificate.spec' in row['validated_reference_declarations'] and
            MODELS[key] in row['validated_reference_declarations'],
            'Reference ownership validation missing')
    require(row['source_float64_scalar'].startswith('fun buffers =>') and
            'LarkBenchmarkFloatAudit.ops' in row['source_float64_scalar'] and
            'LarkBenchmarkFloatAudit.checkedInput' in row['source_float64_scalar'],
            'Source scalar interpretation differs')
    if strategy == 'direct-source-evaluation':
        require(row['source_float64_scalar'] == row['compiled_float64_scalar'],
                'Direct source scalar changed')
    else:
        require(row['compiled_float64_scalar'].startswith('fun buffers scores =>') and
                'LarkBenchmarkFloatAudit.scoreAt scores' in row['compiled_float64_scalar'] and
                'LarkAttention.valueInput' in row['source_float64_scalar'] and
                all(name not in row['compiled_float64_scalar'] for name in
                    ('LarkAttention.valueInput','LarkAttention.probability',
                     'LarkAttention.softInput','LarkAttention.scoreValue')),
                'Materialized scalar source scope differs')
    return row['absolute_error']


def audit_scores(directory, data, metadata, source_bindings):
    cache = directory/'MaterializedScores.json'; oracle = directory/'TorchSoftmaxInput.json'
    actual = read(cache); expected = read(oracle)
    heads, sequence, _ = metadata['buffers'][0]['shape']
    count = heads*sequence*sequence
    require(set(actual) == {'schema','method','count','compiled_source_function','float64_bits'}
            and type(actual['schema']) is int and actual['schema'] == 1 and
            actual['method'] == 'actual-source-scoreValue-materialization' and
            actual['count'] == count and len(actual['float64_bits']) == count,
            'Materialized score scope differs')
    require(set(expected) == {'schema','event','shape','dtype','device','reference_sha256','float64_bits'}
            and type(expected['schema']) is int and expected['schema'] == 1 and
            expected['event'] == 'unchanged-reference-Tensor.softmax-input' and
            expected['shape'] == [heads,sequence,sequence] and expected['dtype'] == 'float64' and
            expected['device'] == 'cpu' and expected['reference_sha256'] == source_bindings['reference.py']
            and len(expected['float64_bits']) == count,'Score oracle scope differs')
    function = actual['compiled_source_function']
    require(function.startswith('fun buffers =>') and
            'LarkBenchmarkFloatAudit.materialize '+str(count) in function and
            'LarkAttention.scoreValue shape LarkBenchmarkFloatAudit.ops' in function and
            'LarkBenchmarkFloatAudit.checkedInput buffers' in function,'Score source function differs')
    binding = data['materialized_score_binding']
    require(set(binding) == {'sha256','count','bytes','source_function'} and
            binding == {'sha256':sha(cache),'count':count,'bytes':cache.stat().st_size,
                        'source_function':function},'Score evidence binding differs')
    maximum = 0.; identical = 0
    for a,b in zip(actual['float64_bits'],expected['float64_bits']):
        value, target = bits(a),bits(b)
        error = abs(value-target)
        require(error <= 1e-10+1e-10*abs(target),'Materialized score comparison failed')
        maximum = max(maximum,error); identical += a == b
    require(data['score_tensor_comparison'] == {
        'comparisons':count,'max_absolute_error':maximum,'bit_identical':identical,
        'oracle_sha256':sha(oracle),'telemetry_preserved_final_outputs':True},
        'Score comparison metrics differ')
    return count


def audit(source, evidence, report):
    require(set(report) == REPORT_KEYS,'Report schema differs')
    require(report['schema'] == 1 and type(report['schema']) is int and
            report['status'] == 'benchmark-reference-numerical-study-matched' and
            report['method'] == METHOD,'Incomplete or different numerical method')
    require(all(report[name] is False for name in FALSE_FLAGS) and
            all(type(report[name]) is int and report[name] == 0
                for name in ('new_certificates','gpu_trials','model_calls')),'Scope inflated')
    require(report['selected_cases'] == list(MODELS) and report['strata'] == STRATA and
            report['sample_count'] == 340 and report['score_comparison_count'] == 589824,
            'Incomplete seventeen-family protocol')
    require(report['maxRecDepth'] == 10000 and report['maxHeartbeats'] == 2000000 and
            report['per_process_timeout_seconds'] == 180 and report['seed'] == 19831 and
            report['storage_conversions'] == 'identity' and
            report['absolute_tolerance'] == report['relative_tolerance'] == 1e-10,
            'Resource, input or numerical comparison protocol differs')
    require(sha(evidence/'source-bindings.json') == SOURCE_BINDINGS_SHA256 ==
            report['source_bindings_sha256'] and report['source_file_count'] == SOURCE_FILE_COUNT,
            'Frozen protocol sources differ')
    source_manifest = read(evidence/'source-bindings.json')
    require({str(path.relative_to(source)) for path in source.rglob('*') if path.is_file()}
            == set(source_manifest),'Unexpected source file')
    verify_files(source,source_manifest)
    require(report['driver_sha256'] == sha(source/HERE/'study.py'),'Measured driver differs')
    require(set(report['module_bindings']) == set(MODULES) and
            all(digest(value) for value in report['module_bindings'].values()),'Module bindings differ')
    for name in MODULES:
        if name.endswith('.lean'):
            require(report['module_bindings'][name] == sha(source/HERE/name) ==
                    sha(evidence/'numerical_modules'/name),'Numerical source differs')
            caps((source/HERE/name).read_text())
        else:
            log = evidence/'numerical_modules'/(name[:-6]+'-compile.log')
            require(log.is_file() and 'error:' not in log.read_text(),'Numerical module did not compile')
    caps((source/HERE/'BenchmarkImports.lean').read_text())
    require(report['import_bindings'] == read(evidence/'checked-imports.json'),'Import receipt differs')
    imports = report['import_bindings']
    require(imports['target'] == 'LarkReal.BenchmarkReferenceImports' and
            imports['source_count'] == 25 and len(imports['compiled']) == 25 and
            imports['lean_version'].startswith('Lean (version 4.19.0,'),'Import scope differs')
    for name, expected in imports['sources'].items():
        if name.endswith('.lean'):
            prefix = 'lean-real/' if name.startswith('LarkReal/') else 'lean/'
            require(sha(source/(prefix+name)) == expected,'Imported source differs')
    audit_controls(source,evidence,report)
    study = load_source_study(source)
    require([case[0] for case in study.CASES] == list(MODELS),'Frozen case registry differs')
    expected_order = [(case[0],stratum) for case in study.CASES for stratum in STRATA]
    require([(case['case'],case['stratum']) for case in report['checks']] == expected_order,
            'Case/stratum roster differs')
    maximum = 0.; score_count = 0
    for case in study.CASES:
        _, metadata, block, owned = study.prepare(case)
        output_count = math.prod(metadata['buffers'][-1]['shape'])
        indices = sorted({0,1,min(127,output_count-2),output_count//2,output_count-1})
        expected_main = ('import BenchmarkFloatAudit\nset_option maxRecDepth 10000\n'
                         'set_option maxHeartbeats 2000000\n')+block
        expected_main += ('benchmark_audit_float @spec from "Input.json" at ['+
                          ','.join(map(str,indices))+']\nend LarkCertificate\n')
        source_bindings = {name:hashlib.sha256(content).hexdigest() for name,content in sorted(owned.items())}
        for stratum in STRATA:
            data = report['checks'][expected_order.index((case[0],stratum))]
            directory = evidence/(case[0]+'-'+stratum)
            strategy = ('source-scoreValue-materialization' if case[0] in ('attention','gqa')
                        else 'direct-source-evaluation')
            extra = {'materialized_score_binding','score_tensor_comparison'} if case[1] == 'attention' else set()
            require(set(data) == CASE_KEYS|extra and data == read(directory/'results.json'),
                    'Case report/schema differs')
            require(data['input_metadata'] == metadata and data['case_source_bindings'] == source_bindings,
                    'Task/reference/source binding differs')
            require(finite(data['seconds']) and 0 <= data['seconds'] <= 180,'Case exceeded process limit')
            require(data['main_sha256'] == sha(directory/'Main.lean') and
                    (directory/'Main.lean').read_text() == expected_main,'Generated Main differs')
            caps(expected_main)
            require(data['input_sha256'] == sha(directory/'Input.json') and
                    data['log_sha256'] == sha(directory/'lean.log'),'Case input/log hash differs')
            inputs(directory/'Input.json',metadata)
            logged = records(directory/'lean.log')
            require('error:' not in (directory/'lean.log').read_text() and len(logged) == 5 and
                    [row['index'] for row in data['samples']] == indices,'Scalar sample roster differs')
            for row, actual, index in zip(data['samples'],logged,indices):
                maximum = max(maximum,audit_sample(row,actual,index,output_count,case[0],strategy))
            if strategy == 'source-scoreValue-materialization':
                score_count += audit_scores(directory,data,metadata,source_bindings)
            else:
                require(not (directory/'MaterializedScores.json').exists() and
                        not (directory/'TorchSoftmaxInput.json').exists(),'Unexpected score cache')
    require(report['max_absolute_error'] == maximum and report['score_comparison_count'] == score_count,
            'Aggregate metrics differ')
    return {'status':'benchmark-reference-packet-audit-passed','samples':340,
            'score_comparisons':score_count,'negative_controls':24,'source_files':SOURCE_FILE_COUNT,
            'max_absolute_error':maximum,'new_certificates':0,'gpu_trials':0,'model_calls':0,
            'original_paper_fully_reproduced':False}


def evidence_names(raw):
    names = []
    for path in raw.rglob('*'):
        if not path.is_file():
            continue
        name = path.relative_to(raw)
        if name.parts[0] == 'source' or path.suffix in ('.olean','.ilean','.pyc','.so'):
            continue
        names.append(name.as_posix())
    return sorted(names)


def verify_layout(names):
    roots = {'results.json','source-bindings.json','checked-imports.json',
             'numerical-controls-driver.log','materialization-controls-driver.log'}
    modules = {'environment.json','BenchmarkRealAudit.lean','BenchmarkFloatAudit.lean',
               'BenchmarkRealAudit-compile.log','BenchmarkFloatAudit-compile.log'}
    cases = {case+'-'+stratum for case in MODELS for stratum in STRATA}
    for name in names:
        parts = safe(name).parts
        if len(parts) == 1:
            require(name in roots,'Unexpected evidence root file')
        elif parts[0] == 'numerical_modules':
            require(len(parts) == 2 and parts[1] in modules,'Unexpected numerical module evidence')
        elif parts[0] in cases:
            allowed = {'Main.lean','Input.json','lean.log','results.json','Progress.log'}
            if parts[0].startswith(('attention-','gqa-')):
                allowed |= {'MaterializedScores.json','TorchSoftmaxInput.json'}
            require(len(parts) == 2 and parts[1] in allowed,'Unexpected case evidence')
        elif parts[0] in ('numerical-controls','materialization-controls'):
            roster = NUMERICAL_NAMES if parts[0] == 'numerical-controls' else CACHE_NAMES
            if len(parts) == 2:
                require(parts[1] == 'results.json','Unexpected control report')
            else:
                require(len(parts) == 3 and parts[1] in roster and
                        parts[2] in {'Main.lean','Input.json','lean.log','Progress.log'},
                        'Unexpected control evidence')
        else:
            raise ValueError('Unexpected evidence directory')


def freeze(raw, output):
    require(not output.exists(),'Packet output already exists')
    report = read(raw/'results.json')
    summary = audit(raw/'source',raw,report)
    names = evidence_names(raw)
    verify_layout(names)
    output.mkdir(parents=True)
    source_manifest = pack(output/'source.tar.gz',raw/'source',read(raw/'source-bindings.json'))
    evidence_manifest = pack(output/'evidence.tar.gz',raw,names)
    write(output/'source-manifest.json',source_manifest)
    require(sha(output/'source-manifest.json') == SOURCE_BINDINGS_SHA256,'Source manifest changed')
    write(output/'evidence-manifest.json',evidence_manifest)
    shutil.copyfile(raw/'results.json',output/'results.json')
    shutil.copyfile(Path(__file__),output/'packet.py')
    files = ['source.tar.gz','evidence.tar.gz','source-manifest.json','evidence-manifest.json',
             'results.json','packet.py']
    manifest = {'schema':1,'status':'frozen-benchmark-reference-study-packet',
                'measurement_source_checkpoint':SOURCE_CHECKPOINT,
                'source_bindings_sha256':SOURCE_BINDINGS_SHA256,
                'files':{name:sha(output/name) for name in files},
                'source_files':len(source_manifest),'evidence_files':len(evidence_manifest),
                'summary':summary}
    write(output/'manifest.json',manifest)
    return manifest


def extract_packet(packet, destination):
    manifest = read(packet/'manifest.json')
    require(set(manifest) == {'schema','status','measurement_source_checkpoint',
                             'source_bindings_sha256','files','source_files','evidence_files','summary'} and
            type(manifest['schema']) is int and manifest['schema'] == 1 and
            manifest['status'] == 'frozen-benchmark-reference-study-packet' and
            manifest['measurement_source_checkpoint'] == SOURCE_CHECKPOINT and
            manifest['source_bindings_sha256'] == SOURCE_BINDINGS_SHA256,'Packet scope differs')
    expected = {'source.tar.gz','evidence.tar.gz','source-manifest.json','evidence-manifest.json',
                'results.json','packet.py'}
    require(set(manifest['files']) == expected and all(digest(x) for x in manifest['files'].values()),
            'Packet file roster differs')
    verify_files(packet,manifest['files'])
    require(sha(packet/'source-manifest.json') == SOURCE_BINDINGS_SHA256,'Source pin differs')
    sources = read(packet/'source-manifest.json'); evidence = read(packet/'evidence-manifest.json')
    require(manifest['source_files'] == len(sources) == SOURCE_FILE_COUNT and
            manifest['evidence_files'] == len(evidence),'Archive file counts differ')
    verify_layout(evidence)
    source_root, evidence_root = destination/'source',destination/'evidence'
    unpack(packet/'source.tar.gz',source_root,sources)
    unpack(packet/'evidence.tar.gz',evidence_root,evidence)
    report = read(evidence_root/'results.json')
    require(report == read(packet/'results.json'),'Packet/evidence reports differ')
    summary = audit(source_root,evidence_root,report)
    require(summary == manifest['summary'],'Packet summary differs')
    return source_root,evidence_root,report,summary


def compare_replay(measured, actual):
    left, right = read(measured/'results.json'),read(actual/'results.json')
    summary = audit(actual/'source',actual,right)
    require(left['selected_cases'] == right['selected_cases'] and left['strata'] == right['strata'],
            'Replay changed the experiment selection')
    score_values = 0
    for a,b in zip(left['checks'],right['checks']):
        require((a['case'],a['stratum'],a['main_sha256'],a['input_sha256']) ==
                (b['case'],b['stratum'],b['main_sha256'],b['input_sha256']),
                'Replay Main/input bytes differ')
        require([(r['index'],r['float64_bits']) for r in a['samples']] ==
                [(r['index'],r['float64_bits']) for r in b['samples']],
                'Replayed scalar values differ')
        if 'score_tensor_comparison' in a:
            name = a['case']+'-'+a['stratum']
            for filename in ('MaterializedScores.json','TorchSoftmaxInput.json'):
                require(read(measured/name/filename)['float64_bits'] ==
                        read(actual/name/filename)['float64_bits'],'Replayed score tensor differs')
            score_values += a['score_tensor_comparison']['comparisons']
    return {'status':'fresh-source-benchmark-replay-bit-identical','case_strata':68,
            'identical_input_files':68,'identical_generated_mains':68,'identical_scalar_values':340,
            'identical_score_values':score_values,'identical_oracle_score_values':score_values,
            'source_bindings_sha256':SOURCE_BINDINGS_SHA256,'recomputed_summary':summary,
            'source_checked_sdk_import_cache_reused':True,'cold_import_rebuild':False,
            'new_certificates':0,'gpu_trials':0,'model_calls':0,'original_paper_fully_reproduced':False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='action',required=True)
    command = sub.add_parser('freeze')
    command.add_argument('--run',required=True,type=Path)
    command.add_argument('--output',required=True,type=Path)
    for name in ('verify','replay'):
        command = sub.add_parser(name)
        command.add_argument('--packet',required=True,type=Path)
        command.add_argument('--output',type=Path,required=name == 'replay')
        if name == 'replay':
            command.add_argument('--lean',required=True,type=Path)
    arguments = parser.parse_args()
    if arguments.action == 'freeze':
        manifest = freeze(arguments.run.resolve(),arguments.output.resolve())
        print(json.dumps(manifest['summary']))
        return
    with tempfile.TemporaryDirectory(prefix='lark-benchmark-packet-') as temporary:
        source,evidence,report,summary = extract_packet(arguments.packet.resolve(),Path(temporary))
        if arguments.action == 'replay':
            output = arguments.output.resolve()
            require(not output.exists(),'Replay output already exists')
            environment = dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
            log_path = output.with_suffix('.driver.log')
            with log_path.open('w') as log:
                run = subprocess.run([sys.executable,str(source/HERE/'study.py'),
                                      '--lean',str(arguments.lean.resolve()),'--output',str(output)],
                                     cwd=source,env=environment,stdout=log,stderr=subprocess.STDOUT)
            require(run.returncode == 0,'Fresh replay failed: '+str(log_path))
            receipt = compare_replay(evidence,output)
            receipt.update(packet_manifest_sha256=sha(arguments.packet/'manifest.json'),
                           measured_report_sha256=sha(arguments.packet/'results.json'),
                           replay_report_sha256=sha(output/'results.json'),
                           replay_driver_log_sha256=sha(log_path),verifier_sha256=sha(Path(__file__)))
            write(output/'replay-verification.json',receipt)
            print(json.dumps(receipt))
        else:
            summary.update(packet_manifest_sha256=sha(arguments.packet/'manifest.json'),
                           verifier_sha256=sha(Path(__file__)))
            if arguments.output:
                arguments.output.mkdir(parents=True,exist_ok=False)
                write(arguments.output/'results.json',summary)
            print(json.dumps(summary))


if __name__ == '__main__':
    main()
