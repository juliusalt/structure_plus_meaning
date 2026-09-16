"""Render complete native development questions, operations and evidence."""
import workflow_json

PRELUDE = workflow_json.PRELUDE + r'''
fun joption f NONE = "null" | joption f (SOME x) = f x;
fun jcondition c = "{\"source\":" ^ jenv (N.condition_source c) ^
  ",\"source_use\":" ^ juse (N.condition_source_use c) ^
  ",\"source_root\":" ^ jaddress (N.condition_source_root c) ^
  ",\"goals\":" ^ jlist jgoal (N.condition_goals c) ^ "}";
fun jdevelopmentQuestion q = "{\"source\":" ^ jenv (N.development_source q) ^
  ",\"source_use\":" ^ juse (N.development_source_use q) ^
  ",\"source_root\":" ^ jaddress (N.development_source_root q) ^
  ",\"generator_entry\":" ^ jsite (N.development_generator_entry q) ^
  ",\"problem\":" ^ jterm (N.development_problem q) ^
  ",\"conditions\":" ^ jlist jcondition (N.development_conditions q) ^
  ",\"scope_criticism\":" ^ jcondition (N.development_scope_criticism q) ^
  ",\"selected_facets\":" ^ jlist jnat (N.development_selected_facets q) ^ "}";
fun jconditionExecution (s,result) = "{\"stage\":" ^ jstage s ^ ",\"result\":" ^ jstageResult result ^ "}";
fun jdevelopmentComparison (rows,(relation,(selected,adequate))) =
  "{\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
  ",\"selected_methods\":" ^ jlist jnat selected ^ ",\"adequate_methods\":" ^ jlist jnat adequate ^ "}";
fun jdevelopmentReport report = "{\"generation\":" ^ jgeneration (N.development_generation report) ^
  ",\"compiled_conditions\":" ^ joption (jlist (joption jstage)) (N.development_compiled_conditions report) ^
  ",\"observed_conditions\":" ^ joption (jlist (joption jconditionExecution)) (N.development_observed_conditions report) ^
  ",\"scope_review\":" ^ joption jconditionExecution (N.development_scope_review report) ^
  ",\"comparison\":" ^ joption jdevelopmentComparison (N.development_comparison report) ^
  ",\"revision\":" ^ joption jcycle (N.development_revision report) ^ "}";
fun jdevelopmentDecision decision = joption (jlist jterm) decision;
fun jdevelopmentResult (report,decision) = "{\"report\":" ^ jdevelopmentReport report ^
  ",\"decision\":" ^ jdevelopmentDecision decision ^ "}";
fun jdevelopmentAssessment (sound,(complete,(ordered,(admitted,whole)))) =
  "{\"sound\":" ^ Bool.toString sound ^ ",\"complete\":" ^ Bool.toString complete ^
  ",\"ordered\":" ^ Bool.toString ordered ^ ",\"admitted\":" ^ Bool.toString admitted ^
  ",\"whole_report\":" ^ Bool.toString whole ^ "}";
fun jdevelopmentAssessed (m,(actual,assessment)) = "{\"method\":" ^ jnat m ^
  ",\"assessment\":" ^ jdevelopmentAssessment assessment ^ ",\"qualities\":" ^
  jlist jquality (map (fn f => (f,N.development_producer_inspect assessment f)) facets) ^ "}";
'''
