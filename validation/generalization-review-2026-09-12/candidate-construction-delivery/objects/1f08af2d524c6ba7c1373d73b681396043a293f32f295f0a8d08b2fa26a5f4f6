from pathlib import Path
import hashlib,json,os
S=Path("/home/julius/structure_and_semantics/validation/generalization-review-2026-09-12/candidate-storage-recovery")
rows=json.loads("[{\"path\":\"/tmp/generalization-quality-review/directed-candidate-construction/application-batch17/native-reader-regression/cases.json\",\"sha256\":\"22cfd6a08d25edadc0075ff4acbdf32cbb91e614ab93cc9c8fece195c8b4f978\",\"bytes\":1067592473},{\"path\":\"/tmp/generalization-quality-review/directed-candidate-construction/application-batch19/native-reader-regression/cases.json\",\"sha256\":\"22cfd6a08d25edadc0075ff4acbdf32cbb91e614ab93cc9c8fece195c8b4f978\",\"bytes\":1067592473},{\"path\":\"/tmp/generalization-quality-review/candidate-delivery-review/retention-validation1/original-reader/cases.json\",\"sha256\":\"22cfd6a08d25edadc0075ff4acbdf32cbb91e614ab93cc9c8fece195c8b4f978\",\"bytes\":1067592473},{\"path\":\"/tmp/generalization-quality-review/candidate-delivery-review/retention-validation1/original-reader/evidence-a38bb5ab-1bdd-4533-bb5c-50498daf7dec/22cfd6a08d25edadc0075ff4acbdf32cbb91e614ab93cc9c8fece195c8b4f978\",\"sha256\":\"22cfd6a08d25edadc0075ff4acbdf32cbb91e614ab93cc9c8fece195c8b4f978\",\"bytes\":1067592473}]")
decision=json.loads("{\"selection\":1,\"criticism\":[\"The complete streaming comparison establishes byte equality of all four current temporary copies with the retained decoded input; the subsequent hash check guards against intervening changes.\",\"The native runs use exactly the same coded finite arguments as their retained checked programs, with the new storage question and concrete subjects recorded separately. Their result is conditional on the independently assessed host operations.\",\"All 118 conditional replays and eight native stages have accepted receipts tied to the actual archive index. The two remaining native stages have no accepted replay receipt and must be resumed in fresh outputs.\",\"Remove only these four task-created duplicates. Preserve the primary archive and the interrupted replay. Measure the actual resource result and retain the entire prospective execution before further work.\"]}")
def digest(path):
 h=hashlib.sha256()
 with path.open("rb") as stream:
  for block in iter(lambda:stream.read(1024*1024),b""):h.update(block)
 return h.hexdigest()
for row in rows:
 p=Path(row["path"])
 assert p.is_file() and not p.is_symlink() and p.stat().st_size==row["bytes"]
 assert digest(p)==row["sha256"]
before=os.statvfs("/tmp")
for row in rows:Path(row["path"]).unlink()
after=os.statvfs("/tmp")
receipt={"decision":decision,"removed_verified_copies":rows,"removed_bytes":sum(r["bytes"] for r in rows),"temporary_filesystem_available_before":before.f_bavail*before.f_frsize,"temporary_filesystem_available_after":after.f_bavail*after.f_frsize,"retained_archive":"validation/generalization-review-2026-09-12/candidate-construction","all_selected_paths_absent":all(not Path(r["path"]).exists() for r in rows)}
(S/"cleanup.json").write_text(json.dumps(receipt,indent=2)+"\n")
print(json.dumps(receipt))
