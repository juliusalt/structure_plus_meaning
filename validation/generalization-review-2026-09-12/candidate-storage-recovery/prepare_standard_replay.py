"""Re-express the already executed recovery arguments in the standard replay receipt format."""
from pathlib import Path
import copy,json,sys
S=Path(__file__).parent;M=Path('/home/julius/structure_and_semantics')
sys.path.insert(0,str(M/'tools'));import investigate
original=json.loads((S/'native-results.json').read_text())
case=copy.deepcopy(original['native_investigations'][0]['case'])
case['evidence']=[{'path':str(p),'sha256':investigate.file_hash(p)} for p in [S/'native-results.json',S/'read_only_native_recovery.py',S/'decision.json']]
boundary='Reexecution of the exact coded conditional problem already run and reviewed before cleanup. Its subjects describe the recorded pre-cleanup state. This produces standard portable replay receipts; it is not a retroactive choice or a claim that the deleted paths still exist.'
spec={'question':case['question'],'boundary':boundary,'problems':[{'name':'retained-storage-recovery','case':case,'required_observations':[[f,0] for f in range(4)]}]}
(S/'standard-investigation.json').write_text(json.dumps(spec,indent=2)+'\n')
