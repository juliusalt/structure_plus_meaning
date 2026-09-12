from pathlib import Path
import copy,gzip,hashlib,json,subprocess,sys
M=Path("/home/julius/structure_and_semantics")
A=M/"validation/generalization-review-2026-09-12/candidate-construction"
S=A.parent/"candidate-storage-recovery"
E=Path("/tmp/generalization-quality-review/candidate-final-replays")
C=Path("/tmp/generalization-quality-review/candidate-delivery-review")
sys.path.insert(0,str(M/"tools"))
import investigate,compare_reasoning_methods as compare,review_investigations as review
def digest(path):
 h=hashlib.sha256()
 with Path(path).open("rb") as stream:
  for block in iter(lambda:stream.read(1024*1024),b""):h.update(block)
 return h.hexdigest()
index=json.loads((A/"index.json").read_text());manifest=json.loads((A/"archive.json").read_text())
copies=[r for r in json.loads((S/"large-retained-copies.json").read_text()) if r["bytes"]>1000000000]
assert len(copies)==4 and len({r["reference"] for r in copies})==1
reference=copies[0]["reference"];assert digest(A/reference)==manifest["files"][reference]
streams=[Path(r["path"]).open("rb") for r in copies];total=0;hashed=hashlib.sha256()
try:
 with gzip.open(A/reference,"rb") as packed:
  for block in iter(lambda:packed.read(1024*1024),b""):
   assert all(f.read(len(block))==block for f in streams)
   total+=len(block);hashed.update(block)
 assert all(f.read(1)==b"" for f in streams)
finally:
 for f in streams:f.close()
assert total==copies[0]["bytes"] and hashed.hexdigest()==copies[0]["sha256"]
native=["application-controls","application-large-7","application-large-8","application-large-9","application-large-10","generic-search","original-guided","native-source","original-reader","finite-presentations"]
completed=[];unfinished=[]
for kind,names in [("investigations",sorted(index["investigations"])),("native",native)]:
 for name in names:
  p=E/kind/name/"replay.json"
  if p.exists():
   result=json.loads(p.read_text());assert result["archive_index_sha256"]==digest(A/"index.json")
   completed.append({"kind":kind,"name":name,"status":result["status"],"receipt_sha256":digest(p)})
  else:unfinished.append({"kind":kind,"name":name})
failures={}
for name in ["batch.log","native--original-reader.log","native--finite-presentations.log"]:
 p=E/name
 if p.exists() and p.stat().st_size<30000:failures[name]=p.read_text()
template=C/"delivery-cleanup-investigation1/preserve-delivery-content"
requirements=["Preserve every original byte in the verified archive.","Remove exactly the four verified temporary duplicates, subject to a final unchanged-byte check.","Restore capacity for the unfinished replay and keep its large outputs within an adequate storage budget.","Preserve the quota failure and resume only unfinished or rejected stages in fresh output directories."]
case=json.loads((template/"initial/case.json").read_text())
expected=[[0,0,0]]+[[f,1,0] for f in range(4)]
assert sorted(case["observations"])==sorted(expected)
case=copy.deepcopy(case)
case["question"]="Recover from the actual replay quota failure without losing any complete input or repeating accepted stages."
case["scope"]={"candidates":{"0":"Leave all temporary copies and repeat the same storage use","1":"Remove the four verified duplicates and retain/resume the identified unfinished stages"},"facets":dict(enumerate(requirements)),"subjects":{"copies":copies,"unfinished":unfinished}}
case["evidence"]=[{"path":str(A/reference),"sha256":manifest["files"][reference]}]
case["semantic_boundary"]="The generic evaluator consumes conditional host-operation claims. Complete streaming comparison establishes the actual byte equality of the four temporary inputs and their retained decoded source. The native table does not itself prove filesystem semantics."
results=[]
for stage in ["initial","followed"]:
 directory=template/stage
 before=json.loads((directory/"receipt.json").read_text())
 ml=(directory/"execute.ML").read_text()
 assert digest(directory/"execute.ML")==before["runtime_program_sha256"]
 assert digest(before["generated_engine"])==before["generated_engine_sha256"]
 assert digest(before["poly"])==before["poly_sha256"]
 native_case=json.loads((directory/"case.json").read_text())
 for key in ["candidates","facets","observations","relation"]:
  assert native_case[key]==case[key]
 if stage=="followed":
  assert native_case["selected"]==results[0]["result"]["revision"]["selection"]
 case["selected"]=native_case["selected"]
 execution=subprocess.run([before["poly"],"--script","/dev/stdin"],input=ml,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=60)
 assert execution.returncode==0,execution.stdout
 lines=[line for line in execution.stdout.splitlines() if line.startswith("INVESTIGATION_RESULT ")]
 assert len(lines)==1
 result=json.loads(lines[0].removeprefix("INVESTIGATION_RESULT "))
 investigate.validate_result(result,"basis")
 mismatches,checked,facts=review.basis_analysis(case,result,case["scope"])
 assert not mismatches,mismatches
 results.append({"stage":stage,"case":copy.deepcopy(case),"program_source":str(directory/"execute.ML"),"program_sha256":before["runtime_program_sha256"],"engine":before["generated_engine"],"engine_sha256":before["generated_engine_sha256"],"poly_sha256":before["poly_sha256"],"result":result,"checked_fields":checked,"facts":facts,"raw_output":execution.stdout})
assessment=compare.assess_candidates(case,results[-1]["result"],[[f,0] for f in range(4)])
print(json.dumps({"byte_comparison":{"copies":copies,"complete_byte_equality":True,"decoded_sha256":hashed.hexdigest(),"bytes_per_copy":total,"reclaimable_bytes":total*len(copies),"retained_reference":reference},"completed":completed,"unfinished":unfinished,"failure_logs":failures,"native_investigations":results,"assessment":assessment},separators=(",",":")))
