"""Stream every original certified-cause scope and reading field."""

PRELUDE = r'''
fun wcauseJudgment (e,(pu,(pr,(au,ar)))) = wobject [
  ("\"environment\"",fn () => wenvironment e),
  ("\"program_use\"",fn () => print (juse pu)),
  ("\"program_address\"",fn () => waddress pr),
  ("\"application_use\"",fn () => print (juse au)),
  ("\"application_address\"",fn () => waddress ar)];
fun wcauseReading (q,(least,(programs,(apps,(replays,(literal,(included,(canonical,words)))))))) = wobject [
  ("\"judgment\"",fn () => wcauseJudgment q),
  ("\"least_judgment_environment\"",fn () => wenvironment least),
  ("\"package_readings\"",fn () => wf (wencoded jprogram) programs),
  ("\"application_readings\"",fn () => wf (wencoded Replay_JSON.japplicationReading) apps),
  ("\"replay_readings\"",fn () => wf (wencoded Replay_JSON.jassertions) replays),
  ("\"literal_application_matches\"",fn () => print (Bool.toString literal)),
  ("\"scope_included\"",fn () => print (Bool.toString included)),
  ("\"canonical_quotation\"",fn () => print (Bool.toString canonical)),
  ("\"byte_valued_use_words\"",fn () => print (Bool.toString words))];
fun wcauseReport (present,(payload,rows)) = wobject [
  ("\"actual_generation\"",fn () => print (Bool.toString present)),
  ("\"payload_matches\"",fn () => print (Bool.toString payload)),
  ("\"scope_readings\"",fn () => wf wcauseReading rows)];
'''
