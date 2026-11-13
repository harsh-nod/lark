"""Archive one finished independent cohort and its completed fresh replay.

This copies recorded evidence and validates the resulting packet. It never
executes captured Python/Lean or invokes a model, hardware or lifecycle action.
"""
import argparse
from datetime import datetime,timezone
import gzip,hashlib,io,json
from pathlib import Path
import shutil,subprocess,sys,tarfile

SOURCES={
 '0e49b6ce519a2af91c81ee60419adcf37357a71fdf904a772dab0cd279368aef':'bb114d8ae61183320242fa5f4463d0cfc727bcd1',
 '05438858483e7f0369e6342ecb9ab0d1f6a6820b982a8dcea270ddb3813f34b1':'1b22551bc295431707dc81288a57ac9a2e6f9475',
}
AUDITOR_SOURCE='1b22551bc295431707dc81288a57ac9a2e6f9475'
COMPARISON_SOURCE='243b7548e294b13f5e6824958e358fe82be21f5e'

def require(ok,message):
 if not ok:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def read(path):return json.loads(path.read_text())
def write(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
def snapshot(root):
 require(root.is_dir() and not any(p.is_symlink() for p in root.rglob('*')),'Input must be an ordinary directory without symlinks')
 return {str(p.relative_to(root)):p.read_bytes() for p in sorted(root.rglob('*')) if p.is_file()}
def digests(files):return {name:sha(data) for name,data in sorted(files.items())}
def archive(root,name,files):
 with (root/(name+'.tar.gz')).open('wb') as target,gzip.GzipFile(filename='',fileobj=target,mode='wb',mtime=0) as compressed:
  with tarfile.open(fileobj=compressed,mode='w') as tar:
   for member,data in sorted(files.items()):
    info=tarfile.TarInfo(member);info.size=len(data);info.mode=0o644;tar.addfile(info,io.BytesIO(data))
 write(root/(name+'-files.json'),digests(files))

def main():
 p=argparse.ArgumentParser(description=__doc__)
 for name in ('repository','recording','audit','lifecycle','output'):p.add_argument('--'+name,type=Path,required=True)
 p.add_argument('--lifecycle-kind',choices=('stop','reuse'),required=True);args=p.parse_args()
 repository,recording,audit,lifecycle,output=(getattr(args,n).resolve() for n in ('repository','recording','audit','lifecycle','output'))
 require(not output.exists() and not any((r/'.git').exists() for r in (output,*output.parents)),'Fresh outside-Git output is required')
 require(not output.is_relative_to(recording) and not output.is_relative_to(audit),'Output must not be inside an input')
 sys.path.insert(0,str(repository))
 from reproduction.local_models import compare_full_shape as comparison
 from reproduction.local_models import audit_full_shape as auditor
 run=comparison.run
 def blob(commit,path):return subprocess.check_output(['git','show',commit+':'+path],cwd=repository,timeout=30)
 require(sha(blob(COMPARISON_SOURCE,'reproduction/local_models/compare_full_shape.py'))==run.sha(Path(comparison.__file__)),'The checked comparison implementation is required')
 raw=read(recording/'results.json');fresh=read(audit/'results.json');life=read(lifecycle)
 require(run.cohort_complete(raw) and raw['complete_17_case_cohort'] is True and raw['test_stub'] is False,'A complete non-stub seventeen-case cohort is required')
 require(raw['runner_sha256'] in SOURCES,'Unknown full-size producer')
 producer=SOURCES[raw['runner_sha256']]
 require(sha(blob(producer,'reproduction/local_models/full_shape_run.py'))==raw['runner_sha256']==run.sha(recording/'runner.py'),'Producer source does not match the recording')
 require(sha(blob(AUDITOR_SOURCE,'reproduction/local_models/audit_full_shape.py'))==fresh['auditor_sha256']==run.sha(Path(auditor.__file__)),'Fresh replay must use the checked auditor source')
 language=run.PREPARATIONS[raw['preparation_manifest_sha256']]
 require(language in auditor.RUNNERS[raw['runner_sha256']] and raw.get('source_language','hip')==language,'Source-language/producer identity differs')
 server=read(recording/'server.json')
 require(all(life[k]==server[k] for k in ('container_id','model','image','gpu_ids')),'Recorded lifecycle belongs to another service')
 require(life.get('model_calls_by_lifecycle_check',0)==0,'Lifecycle check must add no model generations')
 if args.lifecycle_kind=='stop':
  require(life['running'] is False and life.get('other_container_stop_commands_issued',life.get('other_containers_stopped'))==0,'Recorded stop must concern only the exact owned service')
 else:
  require(life['running'] is True and life['retained_for_sequential_cohort'] is True and life['docker_stop_commands_issued']==0,'Explicit retained-service lifecycle evidence is required')
  require(all(life['drained_metrics'].get(k) and all(x==0 for x in life['drained_metrics'][k]) for k in ('num_requests_running','num_requests_waiting')),'Retained service must have been observed drained between cohorts')
 raw_files,audit_files=snapshot(recording),snapshot(audit)
 rows=[comparison.case_summary(case,raw_files,server) for case in raw['cases']]
 winners=[r for r in rows if r['status']=='verified-proof'];requests=sum(r['model_requests'] for r in rows);usage=comparison.sum_usage([r['reported_usage'] for r in rows])
 require(raw['reported_usage']==usage and raw['usage_incomplete'] is False and raw['request_attempts']==raw['response_files']==raw['model_inference_calls']==requests and raw['verified_model_proofs']==len(winners),'Complete recorded usage/counts differ')
 require(fresh['status']=='recorded-full-size-protocol-replayed' and fresh['complete_17_case_cohort'] is True and fresh['recording_results_sha256']==run.sha(recording/'results.json') and fresh['recorded_verified_model_proofs']==fresh['freshly_verified_model_proofs']==len(winners) and len(fresh['fresh_accepted_proof_kernel_checks'])==2*len(winners),'Complete fresh accepted-proof replay is required')
 require(raw['original_paper_fully_reproduced'] is fresh['original_paper_fully_reproduced'] is False,'Original-paper completion overclaim')
 counts={'cases':17,'verified_within_budget':len(winners),'budget_exhausted':17-len(winners),'first_response_verified':sum(r['first_response_verified'] for r in rows),'first_actual_lean_check_verified':sum(r['first_actual_lean_check_verified'] for r in rows),'actual_lean_checks':sum(r['actual_lean_checks'] for r in rows),'model_requests':requests,'response_files':requests,'raw_files':len(raw_files),'audit_files':len(audit_files),'additional_fresh_kernel_checks':2*len(winners)}
 report={'schema':1,'status':'complete-independent-cohort-and-fresh-replay-bound','model':raw['model'],'revision':raw['revision'],'source_language':language,'producer_source_checkpoint':producer,'auditor_source_checkpoint':AUDITOR_SOURCE,'preparation_manifest_sha256':raw['preparation_manifest_sha256'],'counts':counts,'reported_usage':usage,'usage_incomplete':False,'external_api_spend_usd':0,'test_stub':False,'complete_17_case_cohort':True,'new_registered_source_certificates':0,'gpu_trials':0,'original_paper_fully_reproduced':False,'protocol':raw['protocol'],'cases':rows,'metric_definitions':{'first_response_verified':'The first model response already supplied a verified proof; source reads are not first-response successes.','first_actual_lean_check_verified':'First syntax/policy-accepted candidate reaching Lean verified; earlier refusals/reads excluded. This is not first-response or original-paper Pass@1.','verified_within_budget':'Producer and independent fresh audit accepted the proof within16responses/8reads/3actualLeanchecks.'},'scope':'Independent full-size fixed-scaffold proof experiment. All failed attempts and reported usage retained. Model proof completions are not new registered source certificates or original-paper model/registry/harness/NVIDIA results. Archiving reruns no model, Lean or GPU experiment.'}
 preparation='full-shape-preparation-v2' if language=='hip' else 'full-shape-cuda-preparation-v1'
 binding={'schema':1,'raw_results_sha256':run.sha(recording/'results.json'),'audit_results_sha256':run.sha(audit/'results.json'),'raw_runner_sha256':raw['runner_sha256'],'client_sha256':raw['client_sha256'],'auditor_sha256':fresh['auditor_sha256'],'auditor_replay_controller_sha256':fresh['controller_sha256'],'preparation_archive_sha256':run.sha(repository/'reproduction/local_models/results'/preparation/'preparation.tar.gz'),'all_model_requests_bound_to_fixed_protocol':True,'accepted_raw_tactics_bound_to_both_original_and_fresh_Mains':True,'failed_lean_candidates_freshly_rechecked':False,'model_calls_by_auditor':0,'new_model_trials_by_archive':0,'fresh_lean_checks_by_archive':0,'packager_sha256':run.sha(Path(__file__)),'comparison_driver_sha256':run.sha(Path(comparison.__file__)),'packaged_at_utc':datetime.now(timezone.utc).isoformat(),'original_paper_fully_reproduced':False}
 output.mkdir(parents=True,exist_ok=False)
 archive(output,'cohort',raw_files);archive(output,'audit',audit_files)
 shutil.copyfile(recording/'results.json',output/'raw-results.json');shutil.copyfile(audit/'results.json',output/'audit-results.json')
 (output/'lifecycle').mkdir();life_name='stop.json' if args.lifecycle_kind=='stop' else 'service-reuse.json';shutil.copyfile(lifecycle,output/'lifecycle'/life_name)
 write(output/'lifecycle/completion-binding.json',{'cohort_results_sha256':binding['raw_results_sha256'],'audit_results_sha256':binding['audit_results_sha256'],'server_record_sha256':raw['server_record_sha256'],'lifecycle_record_sha256':run.sha(lifecycle),'lifecycle_kind':args.lifecycle_kind,'container_id':server['container_id'],'model_requests':requests,'verified_model_proofs':len(winners),'fresh_accepted_proof_kernel_checks':2*len(winners)})
 write(output/'results.json',report);write(output/'binding.json',binding);shutil.copyfile(__file__,output/'package.py')
 write(output/'manifest.json',{str(p.relative_to(output)):run.sha(p) for p in sorted(output.rglob('*')) if p.is_file()})
 require(digests(snapshot(recording))==digests(raw_files) and digests(snapshot(audit))==digests(audit_files),'Input evidence changed during archiving')
 validated=comparison.load_packet(output)
 require(validated['recorded_counts']==counts and validated['cohort_reported_usage']==usage,'Archived packet did not regenerate the recorded totals')
 print(json.dumps({'status':'complete-cohort-packet-validated','model':raw['model'],'source_language':language,'verified':len(winners),'requests':requests,'raw_files':len(raw_files),'audit_files':len(audit_files),'model_calls_by_archival':0,'fresh_lean_checks_by_archival':0,'original_paper_fully_reproduced':False}))

if __name__=='__main__':main()
