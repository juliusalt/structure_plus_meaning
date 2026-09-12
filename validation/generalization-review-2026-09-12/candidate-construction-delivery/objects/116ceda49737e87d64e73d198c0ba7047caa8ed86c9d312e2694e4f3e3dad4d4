"""Preserve the interrupted state and resume only the two unaccepted stages."""
from pathlib import Path
import hashlib,json,os,subprocess,time
S=Path(__file__).parent;M=Path('/home/julius/structure_and_semantics');A=S.parent/'candidate-construction';E=Path('/tmp/generalization-quality-review/candidate-final-replays')
P=Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64-linux/poly');ENV={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
prior=json.loads((S/'native-results.json').read_text());assert len(prior['completed'])==126 and all(r['status']=='accepted' for r in prior['completed'])
assert prior['unfinished']==[{'kind':'native','name':'original-reader'},{'kind':'native','name':'finite-presentations'}]
partial=[]
for name in ['original-reader','finite-presentations']:
 directory=E/'native'/name
 for p in sorted(directory.rglob('*')):
  if p.is_file():partial.append({'path':str(p.relative_to(E)),'bytes':p.stat().st_size,'symlink':p.is_symlink()})
(S/'interrupted-files.json').write_text(json.dumps({'parent_exit_code':120,'accepted_replays':126,'unfinished':prior['unfinished'],'files':partial},indent=2)+'\n')
steps=[]
for name in ['original-reader','finite-presentations']:
 output=S/'runtime'/name
 command=['python3','-B',M/'tools/replay_reasoning_review.py','--archive',A,'--stage',name,'--poly',P,'--output',output]
 start=time.monotonic()
 with (S/('resume-'+name+'.log')).open('w') as log:
  try:code=subprocess.run(list(map(str,command)),cwd=M,env=ENV,stdout=log,stderr=subprocess.STDOUT,timeout=300).returncode
  except subprocess.TimeoutExpired:code='timeout'
 steps.append({'stage':name,'exit_code':code,'seconds':time.monotonic()-start,'command':list(map(str,command)),'output':str(output)})
(S/'resumed-steps.json').write_text(json.dumps(steps,indent=2)+'\n')
summary={'complete':all(r['exit_code']==0 for r in steps),'preserved_accepted_stages':126,'resumed_stages':steps,'scope':'118 original conditional investigations and all 10 final native stages; complete prior stages are not repeated.'}
(S/'resumed-summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary),flush=True)
raise SystemExit(not summary['complete'])
