"""Stream complete literal replay requests and bounded recorded replay values."""

PRELUDE = r'''
fun wliteralReplay (e,(pu,(pr,(au,(ar,(root,a)))))) = wobject [
  ("\"environment\"",fn () => wenvironment e),
  ("\"program_use\"",fn () => print (juse pu)),
  ("\"program_address\"",fn () => waddress pr),
  ("\"application_use\"",fn () => print (juse au)),
  ("\"application_address\"",fn () => waddress ar),
  ("\"proof_root\"",fn () => print (jsite root)),
  ("\"payload\"",fn () => wartifact (N.finite_artifact_rows a))];
fun wreplayState (n,e) = wobject [
  ("\"next_head\"",fn () => print (jnat n)),
  ("\"environment\"",fn () => wenvironment e)];
fun wreplayValue value = woption (fn (state,(u,(g,(j,c)))) => wobject [
  ("\"state\"",fn () => wreplayState state),
  ("\"use\"",fn () => print (juse u)),
  ("\"generation\"",fn () => wgeneration g),
  ("\"judgment_environment\"",fn () => wenvironment j),
  ("\"quotation\"",fn () => wartifact (N.finite_artifact_rows c))]) value;
fun wreplaySubjectView (input,(l,(rows,replay))) = wobject [
  ("\"state\"",fn () => woption wreplayState input),
  ("\"locus\"",fn () => wtarget l),
  ("\"predecessors\"",fn () => wlist wpredecessor rows),
  ("\"replay\"",fn () => wliteralReplay replay)];
fun wreplayOriginalInput (e,(l,(rows,replay))) = wobject [
  ("\"generation_environment\"",fn () => wenvironment e),
  ("\"locus\"",fn () => wtarget l),
  ("\"predecessors\"",fn () => wlist wpredecessor rows),
  ("\"replay\"",fn () => wliteralReplay replay)];
'''
