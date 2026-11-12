"""Reject altered scope and numerical evidence after bypassing outer packet hashes."""

import argparse
import copy
import json
import math
from pathlib import Path
import shutil
import struct

import packet as audit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    base, out = args.packet.resolve(), args.output.resolve()
    audit.require(not any((p/'.git').exists() for p in (out,*out.parents)), 'Output must be outside Git')
    out.mkdir(parents=True,exist_ok=False)
    audit.verify_files(base,audit.read(base/'manifest.json'))
    audit.unpack(base/'source.tar.gz',out/'source',audit.read(base/'source-manifest.json'))
    audit.unpack(base/'evidence.tar.gz',out/'evidence',audit.read(base/'evidence-manifest.json'))
    source, evidence = out/'source', out/'evidence'
    original = audit.read(base/'results.json')
    positive = audit.audit(source,evidence,original)
    checks = []

    def reject(name, change, expected, *, sync_case=False, files=None):
        report = copy.deepcopy(original)
        restored = {}
        def replace(path, content):
            restored.setdefault(path,path.read_bytes())
            path.write_bytes(content)
        try:
            change(report)
            if files:
                files(report,replace)
            if sync_case:
                row = report['checks'][0]
                replace(evidence/row['case']/row['stratum']/'results.json',
                        (json.dumps(row,indent=2)+'\n').encode())
            try:
                audit.audit(source,evidence,report)
            except ValueError as error:
                audit.require(expected in str(error), f'{name}: unexpected refusal: {error}')
                checks.append({'name':name,'outcome':'refused','message':str(error)})
            else:
                raise ValueError('Altered packet was accepted: '+name)
        finally:
            for path, content in restored.items():
                path.write_bytes(content)

    for name, values, expected in (
        ('invented-original-results',{'original_paper_fully_reproduced':True},'Unsupported numerical-study scope'),
        ('invented-ieee-theorem',{'formal_ieee_or_error_theorem':True},'Unsupported numerical-study scope'),
        ('unknown-ieee-claim',{'ieee_equivalence_proved':True},'Unsupported numerical-study report fields'),
        ('invented-certificate',{'new_certificates':1},'Unsupported numerical-study scope'),
        ('shortened-sample-count',{'samples':239},'Unsupported numerical-study scope'),
        ('boolean-schema',{'schema':True},'Unsupported numerical-study scope'),
        ('loosened-tolerance',{'comparison_atol':.01},'Unsupported numerical-study scope'),
        ('changed-storage-interpretation',{'cast_idealization':'IEEE storage conversions proved exact'},'Storage interpretation differs'),
    ):
        reject(name,lambda report,v=values: report.update(v),expected)
    reject('incomplete-matrix',lambda r:r['checks'].pop(),'Incomplete/duplicate case-stratum matrix')
    reject('duplicate-case',lambda r:r['checks'].__setitem__(1,copy.deepcopy(r['checks'][0])),
           'Incomplete/duplicate case-stratum matrix')
    for name, field, value in (
        ('wrong-family','family','original-authors-production-kernel'),
        ('wrong-output-size','output_elements',1), ('changed-seed','seed',0),
        ('invalid-runtime','lean_seconds',-1),
    ):
        reject(name,lambda r,k=field,v=value:r['checks'][0].__setitem__(k,v),
               'Unsupported case scope/provenance',sync_case=True)
    for name, field in (('wrong-lean-scalar','lean_float64'),('wrong-torch-scalar','torch_ideal_float64')):
        reject(name,lambda r,k=field:r['checks'][0]['samples'][0].__setitem__(
                   k,r['checks'][0]['samples'][0][k]+.25),
               'Float64 numerical comparison failed',sync_case=True)
    reject('wrong-error-summary',lambda r:r['checks'][0].__setitem__('ideal_max_abs_error',.25),
           'Reported numerical difference metrics differ',sync_case=True)
    reject('wrong-reference-binding',lambda r:r['checks'][0].__setitem__('reference_sha256','0'*64),
           'Torch/reference binding differs',sync_case=True)
    reject('wrong-input-binding',lambda r:r['checks'][0].__setitem__('input_sha256','0'*64),
           'Case bytes differ',sync_case=True)

    def change_log(report,replace):
        row = report['checks'][0]
        sample = row['samples'][0]
        value = sample['lean_float64']+.25
        sample['lean_float64'] = value
        sample['float64_bits'] = str(struct.unpack('<Q',struct.pack('<d',value))[0])
        path = evidence/row['case']/row['stratum']/'lean.log'
        changed, lines = False, []
        for line in path.read_text().splitlines():
            if not changed and 'LARK_SPEC_AUDIT ' in line:
                prefix, raw = line.split('LARK_SPEC_AUDIT ',1)
                record = json.loads(raw)
                record['float64_bits'] = sample['float64_bits']
                line = prefix+'LARK_SPEC_AUDIT '+json.dumps(record,separators=(',',':'))
                changed = True
            lines.append(line)
        audit.require(changed,'Missing numerical record for log control')
        replace(path,('\n'.join(lines)+'\n').encode())
        row['lean_log_sha256'] = audit.sha(path)
    reject('rehashed-wrong-log-scalar',lambda r:None,'Float64 numerical comparison failed',
           sync_case=True,files=change_log)

    def append_cap(report,replace):
        row = report['checks'][0]
        path = evidence/row['case']/row['stratum']/'Main.lean'
        replace(path,path.read_bytes()+b'\nset_option maxHeartbeats 3000000\n')
        row['main_sha256'] = audit.sha(path)
    reject('rehashed-extra-cap-override',lambda r:None,'Case options differ',sync_case=True,files=append_cap)

    for name in ('invented-control-certificate','boolean-control-count','duplicate-control-name',
                 'unknown-control-field','empty-refusal-message'):
        def change_control(report,replace,name=name):
            path = evidence/'controls/results.json'
            controls = audit.read(path)
            if name == 'invented-control-certificate': controls['new_certificates'] = 1
            elif name == 'boolean-control-count': controls['positive_controls'] = True
            elif name == 'duplicate-control-name': controls['controls'][-1]['control'] = controls['controls'][-2]['control']
            elif name == 'unknown-control-field': controls['controls'][0]['certified'] = True
            else: controls['controls'][2]['expected_refusal'] = ''
            replace(path,(json.dumps(controls)+'\n').encode())
        expected = ('Unknown control outcome' if name == 'unknown-control-field' else
                    'Control did not refuse as reported' if name == 'empty-refusal-message' else
                    'Control count/status differs')
        reject(name,lambda r:None,expected,files=change_control)
    audit.require(audit.audit(source,evidence,original) == positive,'Control fixtures were not restored')
    report = {'schema':1,'status':'production-reference-packet-controls-passed',
              'packet_manifest_sha256':audit.sha(base/'manifest.json'),'positive_controls':1,
              'negative_controls':len(checks),'checks':checks,
              'mutation_scope':'After archive extraction, bypassing outer hashes; changed case/log hashes and per-case metadata are synchronized where required.',
              'fresh_lean_executions':0,'model_calls':0,'gpu_trials':0,'new_certificates':0,
              'original_paper_fully_reproduced':False}
    audit.write(out/'results.json',report)
    shutil.copyfile(Path(__file__),out/'driver.py')
    shutil.copyfile(Path(audit.__file__),out/'packet.py')
    audit.write(out/'manifest.json',{p.name:audit.sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({'status':report['status'],'negative_controls':len(checks)}))


if __name__ == '__main__':
    main()
