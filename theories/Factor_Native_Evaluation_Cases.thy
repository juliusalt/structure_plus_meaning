theory Factor_Native_Evaluation_Cases
  imports Factor_Finite_Native_Evaluation Factor_Finite_Source_Extension_Cases
    Factor_Finite_Native_Extension_Cases Factor_Program_Evaluation_Investigation
begin

definition native_evaluation_terms where
  "native_evaluation_terms=finsert
    (Finite_Pair (Finite_Pair (Finite_Payload []) (Finite_Payload [])) (Finite_Payload []))
    program_evaluation_terms"

definition native_evaluation_seed where
  "native_evaluation_seed i=(if i<12 then map_option (\<lambda>(E,u,r). (E,u,r,None)) (finite_source_extension_seed i)
    else if i<17 then
      map_option (\<lambda>(F,u). (F,u,[],None))
        (finite_extend_mapped_native (finite_guard_source False) (finite_nat_guard_source_model False)
          (fst (program_evaluation_subject (i+5))) native_guard_source_coordinate)
    else map_option (\<lambda>(F,u,d). (F,u,[],Some d))
      (finite_source_requirement_extension (i=19 \<or> i=20) (i=18 \<or> i=20)))"

definition native_evaluation_report where
  "native_evaluation_report i=map_option (\<lambda>(E,u,r,focus).
    (let source=finite_native_source E u r;
      D=(case source of None \<Rightarrow> {||} | Some P \<Rightarrow>
        ffUnion (fimage (\<lambda>d. fimage (\<lambda>t. (d,t)) native_evaluation_terms) (finite_system_definitions P)));
      details=map_option (\<lambda>P. (finite_system_formed P,finite_program_head_covered P D,
        finite_program_demand_closed P D,finite_program_applications P D,finite_program_rule_table P D)) source
    in (E,u,r,focus,source,D,details,finite_native_program_evaluation E u r D))) (native_evaluation_seed i)"

text \<open>
  The first twelve inputs reuse the previously executed actual native source
  environments, including recursive clauses, material operands, an empty
  package, a missing package and a malformed unused artifact. Five further
  inputs compile the corrected material subjects through the existing package
  constructor. Four inputs reuse its complete checked list and pair plans and
  retain each returned requirement entry as the reported focus.

  Every source is recovered again from its actual artifacts. The requested
  calls use those returned definition sites directly. Complete reports retain
  every environment field, program field, actual requested term, generated
  clause application, rule and answer. The two source meanings and the nested
  data term provide concrete checks of the existing all-term plan contracts.
\<close>

end
