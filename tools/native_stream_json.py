"""Write complete native JSON fields without joining a whole report string."""

PRELUDE = r'''
fun wlist write xs = let
  fun tail [] = () | tail (x::rest) = (print ","; write x; tail rest)
  in print "["; (case xs of [] => () | x::rest => (write x; tail rest)); print "]" end;
fun wobject fields = (print "{";
  let fun field (key,write) = (print key; print ":"; write ())
      fun tail [] = () | tail (x::rest) = (print ","; field x; tail rest)
  in case fields of [] => () | x::rest => (field x; tail rest) end; print "}");
fun woption write NONE = print "null" | woption write (SOME x) = write x;
fun wf write xs = wlist write (elements xs);
fun wencoded encode x = print (encode x);
fun waddress x = wlist (wencoded jnat) x;
fun wedge (r,(s,t)) = wlist waddress [r,s,t];
fun wdata (r,p) = wlist waddress [r,p];
fun wartifact (carrier,(incidence,(counts,functions))) = wobject [
  ("\"carrier\"",fn () => wlist waddress carrier),
  ("\"incidence\"",fn () => wlist wedge incidence),
  ("\"counted_data\"",fn () => wlist wdata counts),
  ("\"functional_data\"",fn () => wlist wdata functions)];
fun wartifactRow (u,a) = (print "["; print (juse u); print ","; wartifact a; print "]");
fun wenvironment e = wobject [
  ("\"artifacts\"",fn () => wlist wartifactRow (N.finite_environment_artifact_rows e)),
  ("\"bindings\"",fn () => wf (wencoded jbinding) (N.finite_environment_bindings e))];
fun wtarget (N.Finite_Whole a) = wobject [
    ("\"whole_artifact\"",fn () => wartifact (N.finite_artifact_rows a))]
  | wtarget (N.Finite_Anchor (a,r)) = wobject [
    ("\"anchored_artifact\"",fn () => (print "[";
      wartifact (N.finite_artifact_rows a); print ","; waddress r; print "]"))];
fun wgeneration g = wobject [
  ("\"locus\"",fn () => wtarget (N.generation_locus g)),
  ("\"predecessors\"",fn () => wf wgeneration (N.generation_predecessors g)),
  ("\"payload\"",fn () => wtarget (N.generation_payload g)),
  ("\"cause\"",fn () => wtarget (N.generation_cause g))];
fun wemit tag write = (print tag; print " "; write (); print "\n"; TextIO.flushOut TextIO.stdOut);
'''
