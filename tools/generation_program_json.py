"""Write complete original generation requests and generation-field readings."""

PRELUDE = r'''
fun wpredecessor (site,g) = wobject [
  ("\"site\"",fn () => print (jsite site)),
  ("\"generation\"",fn () => wgeneration g)];
fun wgenerationProblem (e,(l,(p,(c,rows)))) = wobject [
  ("\"environment\"",fn () => wenvironment e),
  ("\"locus\"",fn () => wtarget l),
  ("\"payload\"",fn () => wtarget p),
  ("\"cause\"",fn () => wtarget c),
  ("\"predecessors\"",fn () => wlist wpredecessor rows)];
fun wsocket (s,d) = wlist waddress [s,d];
fun wgenerationFields (l,(sockets,(p,c))) = wobject [
  ("\"locus\"",fn () => wtarget l),
  ("\"sockets\"",fn () => wf wsocket sockets),
  ("\"payload\"",fn () => wtarget p),
  ("\"cause\"",fn () => wtarget c)];
fun wanchor (site,artifact) = wobject [
  ("\"site\"",fn () => print (jsite site)),
  ("\"artifact\"",fn () => wartifact (N.finite_artifact_rows artifact))];
'''
