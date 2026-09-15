"""Write every original generation-result assessment field and condition value."""

PRELUDE = r'''
fun wgenerationBody (fields,(refs,(l,(p,(c,(preds,(formed,(native,(preserved,original))))))))) = wobject [
  ("\"field_readings\"",fn () => wf wgenerationFields fields),
  ("\"actual_predecessor_sites\"",fn () => wf (wencoded jsite) refs),
  ("\"locus_exact\"",fn () => print (Bool.toString l)),
  ("\"payload_exact\"",fn () => print (Bool.toString p)),
  ("\"cause_exact\"",fn () => print (Bool.toString c)),
  ("\"predecessor_values_exact\"",fn () => print (Bool.toString preds)),
  ("\"environment_formed\"",fn () => print (Bool.toString formed)),
  ("\"native_generation\"",fn () => print (Bool.toString native)),
  ("\"old_environment_preserved\"",fn () => print (Bool.toString preserved)),
  ("\"original_references\"",fn () => print (Bool.toString original))];
fun wgenerationAssessment (ready,(available,body)) = wobject [
  ("\"ready\"",fn () => print (Bool.toString ready)),
  ("\"available\"",fn () => print (Bool.toString available)),
  ("\"result\"",fn () => woption wgenerationBody body)];
'''
