"""Alter source-bound benchmark artifacts after bypassing outer archive hashes."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import struct
import tempfile
import time

HERE = Path(__file__).resolve().parent
specification = importlib.util.spec_from_file_location('benchmark_packet',HERE/'packet.py')
packet = importlib.util.module_from_spec(specification)
specification.loader.exec_module(packet)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',required=True,type=Path)
    parser.add_argument('--output',required=True,type=Path)
    arguments = parser.parse_args()
    arguments.output.mkdir(parents=True,exist_ok=False)
    with tempfile.TemporaryDirectory(prefix='lark-benchmark-packet-controls-') as temporary:
        source,evidence,baseline,positive = packet.extract_packet(arguments.packet,Path(temporary))
        saved = {}
        def write(path,value,raw=False):
            if path not in saved:
                saved[path] = path.read_bytes()
            path.write_text(value if raw else json.dumps(value,indent=2)+'\n')
        def case_folder(data,index):
            row = data['checks'][index]
            return evidence/(row['case']+'-'+row['stratum'])
        def save_case(data,index,log=False):
            row = data['checks'][index]; directory = case_folder(data,index)
            if log:
                added = {'absolute_error','lean_float64','original_dtype_finite',
                         'torch_ideal_float64','torch_original_dtype'}
                lines = ['LARK_SPEC_AUDIT '+json.dumps({key:value for key,value in sample.items()
                          if key not in added},ensure_ascii=False) for sample in row['samples']]
                write(directory/'lean.log','\n'.join(lines)+'\n',raw=True)
                row['log_sha256'] = packet.sha(directory/'lean.log')
            write(directory/'results.json',row)
        def top(key,value):
            return lambda data: data.__setitem__(key,value)
        def sample(key,value,index=0):
            def change(data):
                data['checks'][index]['samples'][0][key] = value
                save_case(data,index,log=True)
            return change
        mutations = [
            ('original-paper-claim',top('original_paper_fully_reproduced',True)),
            ('ieee-claim',top('ieee_equivalence_theorem',True)),
            ('error-bound-claim',top('floating_point_error_bound',True)),
            ('gpu-trial-claim',top('gpu_trials',1)),
            ('model-call-claim',top('model_calls',1)),
            ('new-certificate-claim',top('new_certificates',1)),
            ('missing-family',top('selected_cases',baseline['selected_cases'][:-1])),
            ('missing-stratum',top('strata',baseline['strata'][:-1])),
            ('heartbeat-limit',top('maxHeartbeats',4000000)),
            ('recursion-limit',top('maxRecDepth',20000)),
            ('process-limit',top('per_process_timeout_seconds',360)),
            ('seed',top('seed',19832)),
            ('storage-casts',top('storage_conversions','rounded-float16')),
            ('tolerance',top('absolute_tolerance',1e-2)),
            ('aggregate-error',top('max_absolute_error',1.0)),
            ('extra-report-field',top('original_nvidia_results_reproduced',True)),
            ('sample-index',sample('index',7)),
            ('output-shape',sample('output_count',1)),
            ('sample-method',sample('method','synthetic-formula')),
            ('real-type',sample('elaborated_real_type','List Nat')),
            ('real-expression',sample('elaborated_real_expression','fabricated reference')),
            ('compiled-scalar',sample('compiled_float64_scalar','fun buffers => 0')),
            ('wrong-strategy',sample('evaluation_strategy','source-scoreValue-materialization')),
        ]
        def duplicate(data):
            data['checks'][1] = copy.deepcopy(data['checks'][0])
        mutations.append(('duplicate-case',duplicate))
        def wrong_value(data):
            row = data['checks'][0]['samples'][0]
            value = row['torch_ideal_float64']+1
            row['float64_bits'] = str(struct.unpack('<Q',struct.pack('<d',value))[0])
            row['lean_float64'] = value; row['absolute_error'] = 1.0
            data['max_absolute_error'] = 1.0
            save_case(data,0,log=True)
        mutations.append(('synchronized-numerical-mismatch',wrong_value))
        def ownership(data):
            data['checks'][0]['samples'][0]['validated_reference_declarations'].remove('LarkCertificate.spec')
            save_case(data,0,log=True)
        mutations.append(('reference-ownership',ownership))
        attention = next(i for i,row in enumerate(baseline['checks']) if row['case'] == 'attention')
        def changed_cache(data,field,value):
            directory = case_folder(data,attention); path = directory/'MaterializedScores.json'
            content = packet.read(path)
            if field == 'value':
                content['float64_bits'][0] = value
            else:
                content[field] = value
            write(path,content)
            binding = data['checks'][attention]['materialized_score_binding']
            binding['sha256'] = packet.sha(path); binding['bytes'] = path.stat().st_size
            save_case(data,attention)
        mutations.extend([
            ('score-cache-value',lambda data: changed_cache(data,'value',
                str(struct.unpack('<Q',struct.pack('<d',123.0))[0]))),
            ('score-cache-nonfinite',lambda data: changed_cache(data,'value','9218868437227405312')),
            ('score-cache-method',lambda data: changed_cache(data,'method','copied-python-formula')),
        ])
        def oracle(data,field,value):
            directory = case_folder(data,attention); path = directory/'TorchSoftmaxInput.json'
            content = packet.read(path); content[field] = value; write(path,content)
            data['checks'][attention]['score_tensor_comparison']['oracle_sha256'] = packet.sha(path)
            save_case(data,attention)
        mutations.extend([
            ('oracle-dtype',lambda data: oracle(data,'dtype','float32')),
            ('oracle-reference',lambda data: oracle(data,'reference_sha256','0'*64)),
            ('oracle-device',lambda data: oracle(data,'device','cuda')),
        ])
        def metric(data,field,value):
            data['checks'][attention]['score_tensor_comparison'][field] = value
            save_case(data,attention)
        mutations.extend([
            ('score-count',lambda data: metric(data,'comparisons',1)),
            ('score-bit-count',lambda data: metric(data,'bit_identical',0)),
            ('telemetry-changed-output',lambda data: metric(data,'telemetry_preserved_final_outputs',False)),
        ])
        def input_change(data,kind):
            directory = case_folder(data,0); path = directory/'Input.json'; content = packet.read(path)
            if kind == 'shape':
                content['buffers'][0].pop()
            elif kind == 'dtype':
                content['buffers'][0][0] = str(struct.unpack('<Q',struct.pack('<d',.123456789))[0])
            else:
                content['unexpected'] = True
            write(path,content); data['checks'][0]['input_sha256'] = packet.sha(path); save_case(data,0)
        mutations.extend((name,lambda data,kind=kind: input_change(data,kind)) for name,kind in
                         [('input-shape','shape'),('input-storage-quantization','dtype'),('input-schema','schema')])
        def main_limit(data):
            path = case_folder(data,0)/'Main.lean'
            write(path,path.read_text()+'set_option maxHeartbeats 2000000\n',raw=True)
            data['checks'][0]['main_sha256'] = packet.sha(path); save_case(data,0)
        mutations.append(('extra-main-limit-override',main_limit))
        def control(data):
            path = evidence/'numerical-controls/results.json'; content = packet.read(path)
            content['controls'][-1]['exit_code'] = 0; write(path,content)
            data['controls']['numerical']['report_sha256'] = packet.sha(path)
        mutations.append(('accepted-refusal-control',control))
        def source_pin(data):
            path = source/packet.HERE/'BenchmarkFloatAudit.lean'
            write(path,path.read_text()+'\n-- altered source\n',raw=True)
            manifest = packet.read(evidence/'source-bindings.json')
            manifest[packet.HERE+'BenchmarkFloatAudit.lean'] = packet.sha(path)
            write(evidence/'source-bindings.json',manifest)
            data['source_bindings_sha256'] = packet.sha(evidence/'source-bindings.json')
        mutations.append(('synchronized-source-pin',source_pin))
        results = []
        for name, mutate in mutations:
            data = copy.deepcopy(baseline); start = time.monotonic()
            try:
                mutate(data); write(evidence/'results.json',data)
                try:
                    packet.audit(source,evidence,data)
                except (ValueError,KeyError,TypeError,OverflowError) as error:
                    results.append({'control':name,'outcome':'rejected',
                                    'reason':str(error),'seconds':time.monotonic()-start})
                else:
                    raise RuntimeError('Altered packet accepted: '+name)
            finally:
                for path, content in saved.items():
                    path.write_bytes(content)
                saved.clear()
            print(json.dumps(results[-1]),flush=True)
        packet.audit(source,evidence,baseline)
        report = {'status':'benchmark-packet-mutation-controls-passed',
                  'negative_controls':len(results),'controls':results,
                  'positive_before_and_after':True,'outer_archive_hashes_bypassed':True,
                  'changed_case_and_log_hashes_synchronized':True,
                  'packet_manifest_sha256':packet.sha(arguments.packet/'manifest.json'),
                  'verifier_sha256':packet.sha(HERE/'packet.py'),
                  'driver_sha256':packet.sha(Path(__file__)), 'original_paper_fully_reproduced':False}
        packet.write(arguments.output/'results.json',report)


if __name__ == '__main__':
    main()
