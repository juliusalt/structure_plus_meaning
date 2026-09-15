theory Shared_Investigation_Cycles
  imports Finite_Assessed_Investigation
begin

definition shared_investigation_cycle where
  "shared_investigation_cycle cs fs rows relation selected=(let
    initial=investigation_basis cs fs selected rows relation;
    repairs=investigation_repairs cs fs selected rows relation;
    retained=investigation_retain cs fs selected rows relation;
    withdrawn=filter (\<lambda>f. f\<notin>set retained) (remdups selected);
    available=(if retained=selected then repairs else investigation_repairs cs fs retained rows relation);
    revision_repairs=fst (snd (snd available));
    revised=investigation_extend retained revision_repairs;
    following=(if revised=selected then initial else investigation_basis cs fs revised rows relation);
    revision=(retained,withdrawn,revision_repairs,revised,fst (snd following))
    in (selected,initial,repairs,revision,following))"

theorem shared_investigation_cycle_exact:
  "shared_investigation_cycle cs fs rows relation selected=
    investigation_cycle_report cs fs rows relation selected"
  by (simp add: shared_investigation_cycle_def investigation_cycle_report_def
    investigation_revision_def Let_def)

declare investigation_cycle_report_def[code del]

lemma investigation_cycle_shared_code [code]:
  "investigation_cycle_report cs fs rows relation selected=
    shared_investigation_cycle cs fs rows relation selected"
  by (rule shared_investigation_cycle_exact[symmetric])

text \<open>The actual retained and revised facet lists control reuse of
  complete reports. A changed list executes its own original calculation.
  The followed basis supplies the revision's residual as well as its complete
  final report, so that same basis is not independently rebuilt. Every original
  repair, withdrawal, revised facet, residual and report remains in the equation.\<close>

end
