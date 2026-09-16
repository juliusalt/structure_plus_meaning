"""Render complete source-change requests, native operations and admission evidence."""
import native_development_json

PRELUDE = native_development_json.PRELUDE + r'''
fun jsteeredSourceResult (m,(Q,(report,(claim,admission)))) = "{\"method\":" ^ jnat m ^
  ",\"question\":" ^ jdevelopmentQuestion Q ^ ",\"report\":" ^ jdevelopmentReport report ^
  ",\"claim\":" ^ jdevelopmentDecision claim ^ ",\"admission\":" ^ jdevelopmentDecision admission ^ "}";
fun jsourceProposal (q,e) = "{\"program\":" ^ jprogram q ^ ",\"entry\":" ^ jsite e ^ "}";
fun jsourceRequest r = "{\"source\":" ^ jenv (N.source_development_environment r) ^
  ",\"source_use\":" ^ juse (N.source_development_use r) ^
  ",\"source_root\":" ^ jaddress (N.source_development_root r) ^
  ",\"targets\":" ^ jlist jsourceProposal (N.source_development_targets r) ^
  ",\"input\":" ^ jterm (N.source_development_input r) ^
  ",\"outputs\":" ^ jlist jterm (N.source_development_outputs r) ^ "}";
fun jsourceInstalled (d,(e,u)) = "{\"entry\":" ^ jsite d ^
  ",\"environment\":" ^ jenv e ^ ",\"selector\":" ^ juse u ^ "}";
fun jsourceObservation (i,values) = "[" ^ jnat i ^ "," ^ jlist Bool.toString values ^ "]";
fun jsourceReport r = "{\"proposals\":" ^ jlist jsourceProposal (N.source_report_proposals r) ^
  ",\"observations\":" ^ jlist jsourceObservation (N.source_report_observations r) ^
  ",\"question\":" ^ joption jdevelopmentQuestion (N.source_report_question r) ^
  ",\"execution\":" ^ joption jsteeredSourceResult (N.source_report_execution r) ^
  ",\"selected\":" ^ joption jsourceProposal (N.source_report_selected r) ^
  ",\"installed\":" ^ joption jsourceInstalled (N.source_report_installed r) ^
  ",\"stage\":" ^ joption jstage (N.source_report_stage r) ^
  ",\"query\":" ^ joption jstageResult (N.source_report_query r) ^ "}";
fun jsourceAdmission result = joption
  (fn (proposal,(installed,query)) => "{\"proposal\":" ^ jsourceProposal proposal ^
    ",\"installed\":" ^ jsourceInstalled installed ^ ",\"query\":" ^ jstageResult query ^ "}") result;
fun jsourcePacket (request,(report,admission)) = "{\"request\":" ^ jsourceRequest request ^
  ",\"report\":" ^ jsourceReport report ^ ",\"admission\":" ^ jsourceAdmission admission ^ "}";
fun jsourceControl (i,(report,admission)) = "{\"control\":" ^ jnat i ^ ",\"report\":" ^ jsourceReport report ^
  ",\"admission\":" ^ jsourceAdmission admission ^ "}";
'''
