"""Physical timing around unchanged complete native operations and reporting."""

PRELUDE = r'''
fun native_stage_timed name action = let
  val elapsed = Timer.startRealTimer ();
  val cpu = Timer.startCPUTimer ();
  val result = action ();
  val {usr,sys} = Timer.checkCPUTimer cpu;
  val () = print ("Physicalstage " ^ name ^ " wall=" ^ Time.toString (Timer.checkRealTimer elapsed) ^
    " user=" ^ Time.toString usr ^ " system=" ^ Time.toString sys ^ "\n");
  in result end;
'''

REPORT_START = '\nval physical_report_clock = Timer.startRealTimer ();\n'
REPORT_END = r'''
val () = print ("Physicalstage reporting wall=" ^ Time.toString (Timer.checkRealTimer physical_report_clock) ^ "\n");
'''
