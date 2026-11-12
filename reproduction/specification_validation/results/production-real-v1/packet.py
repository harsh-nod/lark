"""Freeze, audit, or recompute a source-only elaborated-reference study packet."""

import argparse
import gzip
import hashlib
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


CASE_FOLDERS = {
    'silu':'production_silu/cases/partial_wave',
    'weighted-rmsnorm':'production_rmsnorm/cases/weighted_16384',
    'fused-rmsnorm':'production_fused_rmsnorm/cases/native_16384',
    'attention':'online_attention/cases/native_fp16',
    'rope-interleaved':'production_rope/cases/interleaved',
    'rope-split':'production_rope/cases/split-half',
    'qknorm-interleaved':'production_qknorm_rope/cases/interleaved',
    'qknorm-split':'production_qknorm_rope/cases/split-half',
    'flashinfer-rmsnorm':'production_flashinfer_rmsnorm/cases/native_16384',
    'sglang-rmsnorm':'production_sglang_rmsnorm/cases/native_fixed',
    'awq':'production_awq_gemm/cases/m17_k32_n64',
    'softmax-reference':'production_softmax/cases/native_fixed',
}
STRATA = ['dyadic','normal','basis','cancellation']
CAPS = ('set_option maxRecDepth 10000\n','set_option maxHeartbeats 2000000\n')
FAMILIES = dict(zip(CASE_FOLDERS, (
    'vllm-silu','vllm-rmsnorm','fused-add-rmsnorm','native-attention',
    'vllm-rope','vllm-rope','fused-qknorm-rope','fused-qknorm-rope',
    'flashinfer-rmsnorm','sglang-rmsnorm','vllm-awq','llmc-softmax-reference')))
CONTROL_NAMES = ('positive','semantic-doubling','unsupported-operation','wrong-element-type',
                 'output-index','input-buffer','input-offset','zero-denominator','negative-sqrt',
                 'nonfinite-input','nonfinite-intermediate','unknown-input-schema',
                 'noncanonical-add','noncanonical-literal','noncanonical-append')
REFUSALS = dict(zip(CONTROL_NAMES[2:], (
    'reference-audit unsupported declaration: Real.sin',
    'reference-audit expected List Real', 'reference-audit output index out of bounds',
    'reference-audit input index out of bounds','reference-audit input index out of bounds',
    'reference-audit zero denominator','reference-audit negative square-root input',
    'reference-audit non-finite input','reference-audit non-finite intermediate',
    'reference-audit unknown input schema', *(['reference-audit unsupported primitive instance']*3))))


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


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
                    and entry.size <= 10_000_000 and not any(p in ('.git','.lake') for p in name.parts)
                    and not entry.name.endswith(('.olean','.ilean','.so','.pyc')), 'Unexpected archive entry')
            total += entry.size
            require(total <= 100_000_000, 'Archive exceeds evidence/source bound')
            blob = stream.extractfile(entry).read()
            require(hashlib.sha256(blob).hexdigest() == manifest[entry.name], 'Archived bytes differ')
            path = destination/name
            path.parent.mkdir(parents=True,exist_ok=True)
            path.write_bytes(blob)
            seen.add(entry.name)
    require(seen == set(manifest), 'Incomplete archive')


def logs(path):
    raw = path.read_text()
    require('error:' not in raw, 'Successful study contains a Lean error')
    return [json.loads(line.split('LARK_SPEC_AUDIT ',1)[1])
            for line in raw.splitlines() if 'LARK_SPEC_AUDIT ' in line]


def correct_caps(text):
    # Refuse extra overrides as well as changed values in these new files.
    options = re.findall(r'\bset_option\s+(?:maxRecDepth|maxHeartbeats)[^\n]*',text)
    return options == [c.rstrip('\n') for c in CAPS]


def audit(source, evidence, report):
    fixed = {'schema':2,'status':'elaborated-production-references-matched-on-samples',
             'families':10,'variants':12,'samples':240,'device':'cpu',
             'new_certificates':0,'formal_ieee_or_error_theorem':False,
             'original_paper_fully_reproduced':False,'model_calls':0,'gpu_trials':0,
             'comparison_atol':1e-10,'comparison_rtol':1e-10,
             'strata':STRATA,'selected_cases':list(CASE_FOLDERS),'positive_controls':1,'negative_controls':14}
    extra = {'checks','torch_version','module_compilation','reference_imports','source_bindings',
             'lean_version','lean_binary_sha256','python','platform','cast_idealization'}
    require(type(report) is dict and set(report) == set(fixed)|extra,
            'Unsupported numerical-study report fields')
    for key, expected in fixed.items():
        require(type(report.get(key)) is type(expected) and report[key] == expected,
                'Unsupported numerical-study scope: '+key)
    require(type(report['lean_version']) is str and re.match(r'Lean \(version 4\.19\.0(?:,|\))',report['lean_version']),
            'Unpinned Lean version')
    require(all(type(report[k]) is str and bool(report[k]) for k in ('torch_version','python','platform')),
            'Missing numerical runtime provenance')
    require(type(report['module_compilation']) is dict
            and set(report['module_compilation']) == {'source_sha256','olean_sha256'}
            and all(type(h) is str and re.fullmatch('[0-9a-f]{64}',h)
                    for h in (*report['module_compilation'].values(),report['lean_binary_sha256'])),
            'Invalid compiler provenance')
    require(report['cast_idealization'] == 'Explicit float/half/floating to()/dtype conversions are identities for the float64 Torch track; original dtype outputs are reported separately.',
            'Storage interpretation differs')
    verify_files(source,report['source_bindings'])
    require(report['source_bindings'] == read(evidence/'source-bindings.json'), 'Source inventory differs')
    module = source/'reproduction/specification_validation/SpecAudit.lean'
    require(sha(module) == report['module_compilation']['source_sha256'], 'Numerical module differs')
    require(correct_caps(module.read_text()), 'Numerical module options differ')
    require('checkPrimitive' in module.read_text(), 'Missing primitive instance guards')
    require('error:' not in (evidence/'compile.log').read_text(), 'Numerical compilation failed')
    controls = read(evidence/'controls/results.json')
    require(set(controls) == {'schema','status','positive_controls','negative_controls','controls','new_certificates'}
            and type(controls['schema']) is int and controls['schema'] == 1
            and type(controls['new_certificates']) is int and controls['new_certificates'] == 0
            and controls['status'] == 'numerical-auditor-controls-passed'
            and type(controls['positive_controls']) is int
            and controls['positive_controls'] == 1
            and type(controls['negative_controls']) is int
            and controls['negative_controls'] == report['negative_controls']
            and [r['control'] for r in controls['controls']] == list(CONTROL_NAMES), 'Control count/status differs')
    for row in controls['controls']:
        path = evidence/'controls'/safe(row['control'])
        text = (path/'lean.log').read_text()
        require(correct_caps((path/'Main.lean').read_text()), 'Control options differ')
        require(type(row['seconds']) in (int,float) and math.isfinite(row['seconds']) and row['seconds'] >= 0,
                'Invalid control runtime')
        if row['outcome'] == 'refused':
            require(set(row) == {'control','exit_code','seconds','outcome','expected_refusal'}
                    and type(row['exit_code']) is int and row['exit_code'] == 1
                    and row['control'] not in ('positive','semantic-doubling')
                    and row['expected_refusal'] == REFUSALS[row['control']]
                    and row['expected_refusal'] in text and 'LARK_SPEC_AUDIT ' not in text,
                    'Control did not refuse as reported')
        else:
            require(set(row) == {'control','exit_code','seconds','outcome','lean_float64','independent_expected'}
                    and ((row['control'],row['outcome']) in (
                        ('positive','matched'),('semantic-doubling','numerical-mismatch-detected'))),
                    'Unknown control outcome')
            found = logs(path/'lean.log')
            require(row['exit_code'] == 0 and len(found) == 1, 'Positive/mutation control did not evaluate')
            value = struct.unpack('<d',struct.pack('<Q',int(found[0]['float64_bits'])))[0]
            require(value == row['lean_float64'] and row['independent_expected'] == 1.25,
                    'Toy oracle control differs')
            require((abs(value-1.25) <= 1e-10+1e-10*1.25) == (row['outcome'] == 'matched'),
                    'Toy semantic mutation was not detected')
    expected_order = [(case,stratum) for case in CASE_FOLDERS for stratum in STRATA]
    require([(r['case'],r['stratum']) for r in report['checks']] == expected_order,
            'Incomplete/duplicate case-stratum matrix')
    require(type(report['reference_imports']) is dict and set(report['reference_imports']) == set(CASE_FOLDERS),
            'Incomplete reference import provenance')
    for imported in report['reference_imports'].values():
        require(set(imported) == {'sources','compiled'} and bool(imported['sources'])
                and set(imported['compiled']) == {str(PurePosixPath(n).with_suffix('.olean')) for n in imported['sources']},
                'Reference source/compiled inventory differs')
        for name, expected in imported['sources'].items():
            prefix = 'lean-real/' if name.startswith('LarkReal/') else 'lean/'
            require(sha(source/prefix/safe(name)) == expected, 'Reference import source differs')
        require(all(type(h) is str and re.fullmatch('[0-9a-f]{64}',h) for h in imported['compiled'].values()),
                'Invalid compiled reference import hashes')
    for row in report['checks']:
        folder = source/'reproduction'/CASE_FOLDERS[row['case']]
        path = evidence/row['case']/row['stratum']
        task = read(folder/'task.json')
        output_elements = sum(math.prod(b['shape']) for b in task['buffers'] if b['role'] in ('output','inout'))
        require(set(row) == {'case','family','stratum','samples','reference_sha256','task_sha256','input_sha256',
                            'main_sha256','lean_log_sha256','lean_seconds','reference_executed_unchanged',
                            'output_elements','ideal_max_abs_error','native_max_abs_difference','seed','input_stratum'}
                and row['family'] == FAMILIES[row['case']] and row['input_stratum'] == row['stratum']
                and type(row['output_elements']) is int and row['output_elements'] == output_elements
                and type(row['seed']) is int and row['seed'] == 7321+list(CASE_FOLDERS).index(row['case'])*1009
                and type(row['lean_seconds']) in (int,float) and math.isfinite(row['lean_seconds']) and row['lean_seconds'] >= 0,
                'Unsupported case scope/provenance')
        require(row['reference_executed_unchanged'] is True
                and sha(folder/'reference.py') == row['reference_sha256']
                and sha(folder/'task.json') == row['task_sha256'], 'Torch/reference binding differs')
        for name, key in (('Input.json','input_sha256'),('Main.lean','main_sha256'),('lean.log','lean_log_sha256')):
            require(sha(path/name) == row[key], 'Case bytes differ: '+str(path/name))
        require(read(path/'results.json') == row, 'Aggregate/per-case results differ')
        require(correct_caps((path/'Main.lean').read_text()), 'Case options differ')
        found = logs(path/'lean.log')
        indices = sorted({0,1,min(127,row['output_elements']-1),row['output_elements']//2,row['output_elements']-1})
        require(len(found) == 5 and [r['index'] for r in row['samples']] == indices,
                'Output sample selection differs')
        for actual, sample in zip(found,row['samples']):
            require(all(sample.get(k) == v for k,v in actual.items())
                    and actual['elaborated_type'] == 'List ℝ', 'Elaborated expression/log binding differs')
            value = struct.unpack('<d',struct.pack('<Q',int(actual['float64_bits'])))[0]
            require(math.isfinite(value) and value == sample['lean_float64']
                    and math.isfinite(sample['torch_ideal_float64'])
                    and math.isfinite(sample['torch_original_dtype'])
                    and abs(value-sample['torch_ideal_float64']) <= 1e-10+1e-10*abs(sample['torch_ideal_float64']),
                    'Float64 numerical comparison failed')
        require(row['ideal_max_abs_error'] == max(abs(s['lean_float64']-s['torch_ideal_float64']) for s in row['samples'])
                and row['native_max_abs_difference'] == max(abs(s['lean_float64']-s['torch_original_dtype']) for s in row['samples']),
                'Reported numerical difference metrics differ')
    return {'status':'frozen-numerical-evidence-audit-passed','variants':12,'families':10,
            'strata':4,'samples':240,'negative_controls':report['negative_controls'],
            'fresh_lean_executions':0,'new_certificates':0,'original_paper_fully_reproduced':False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('action',choices=('freeze','verify','recompute'))
    parser.add_argument('--study',type=Path)
    parser.add_argument('--packet',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--lean',type=Path)
    parser.add_argument('--dependency-project',type=Path)
    args = parser.parse_args()
    out = args.output.resolve()
    require(not any((p/'.git').exists() for p in (out,*out.parents)), 'Output must be outside Git')
    out.mkdir(parents=True,exist_ok=False)
    if args.action == 'freeze':
        require(args.study is not None, '--study required')
        study = args.study.resolve()
        report = read(study/'results.json')
        audit(study/'source',study,report)
        source_manifest = pack(out/'source.tar.gz',study/'source',report['source_bindings'])
        evidence = ['compile.log','source-bindings.json','controls/results.json']
        evidence += [str(p.relative_to(study)) for p in (study/'controls').rglob('*') if p.is_file() and p.name != 'results.json']
        for row in report['checks']:
            evidence += [f"{row['case']}/{row['stratum']}/{name}"
                         for name in ('Input.json','Main.lean','lean.log','results.json')]
        evidence_manifest = pack(out/'evidence.tar.gz',study,sorted(set(evidence)))
        write(out/'source-manifest.json',source_manifest)
        write(out/'evidence-manifest.json',evidence_manifest)
        shutil.copyfile(study/'results.json',out/'results.json')
        shutil.copyfile(Path(__file__),out/'packet.py')
        write(out/'manifest.json',{p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file()})
        print(json.dumps({'status':'source-only-numerical-study-frozen','source_files':len(source_manifest),
                          'evidence_files':len(evidence_manifest),'samples':report['samples']}))
        return
    require(args.packet is not None, '--packet required')
    packet = args.packet.resolve()
    manifest = read(packet/'manifest.json')
    require(set(manifest) == {'source.tar.gz','source-manifest.json','evidence.tar.gz',
                              'evidence-manifest.json','results.json','packet.py'}, 'Packet file set differs')
    verify_files(packet,manifest)
    unpack(packet/'source.tar.gz',out/'source',read(packet/'source-manifest.json'))
    unpack(packet/'evidence.tar.gz',out/'evidence',read(packet/'evidence-manifest.json'))
    report = read(packet/'results.json')
    result = audit(out/'source',out/'evidence',report)
    if args.action == 'recompute':
        require(args.lean is not None and args.dependency_project is not None,
                '--lean and --dependency-project required for recompute')
        env = dict(os.environ,LARK_REAL_PROJECT=str(args.dependency_project.resolve()))
        for name in ('CUDA_VISIBLE_DEVICES','HIP_VISIBLE_DEVICES','ROCR_VISIBLE_DEVICES'):
            env[name] = ''
        with (out/'recompute.log').open('w') as log:
            run = subprocess.run([sys.executable,str(out/'source/reproduction/specification_validation/study.py'),
                                  '--lean',str(args.lean.absolute()),'--output',str(out/'recomputed')],
                                 env=env,stdout=log,stderr=subprocess.STDOUT)
        require(run.returncode == 0, 'Fresh numerical recomputation failed; inspect recompute.log')
        fresh = read(out/'recomputed/results.json')
        audit(out/'recomputed/source',out/'recomputed',fresh)
        for old, new in zip(report['checks'],fresh['checks']):
            require(old['input_sha256'] == new['input_sha256'], 'Recomputed input stream differs')
            for x,y in zip(old['samples'],new['samples']):
                require(abs(x['lean_float64']-y['lean_float64']) <= 1e-10+1e-10*abs(x['lean_float64']),
                        'Recomputed Lean scalar differs')
        result.update(status='source-only-numerical-recomputation-passed',
                      fresh_lean_executions=1+48+len(read(out/'recomputed/controls/results.json')['controls']),
                      execution_count_scope='Direct numerical module/control/case Lean processes; SDK import-cache builds are additional.')
    write(out/'results.json',result)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
