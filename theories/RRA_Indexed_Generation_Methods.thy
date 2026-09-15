theory RRA_Indexed_Generation_Methods
  imports RRA_Indexed_Generation_Reports
begin

definition generation_shallow_check where
  "generation_shallow_check read_fields G u r=(case G of Generation l P p c \<Rightarrow>
    fBex (read_fields u r) (\<lambda>(l',M,p',c'). l=l' \<and> p=p' \<and> c=c'))"

definition indexed_generation_variant_key :: "nat\<Rightarrow>nat" where
  "indexed_generation_variant_key m=(if m\<in>{2,3,4,7} then m else 0)"

definition indexed_generation_variant where
  "indexed_generation_variant (m::nat) X=(case X of (input,l,p,c,rows,queries) \<Rightarrow>
    finite_prepared_results (\<lambda>q.
      if m=2 then generation_reading_report
        (lookup_generation_field_readings (digit_allocated_artifacts q) (\<lambda>u r. {||}))
        (\<lambda>G. lookup_check_generation G (digit_allocated_artifacts q) (\<lambda>u r. {||}))
        (digit_generation_anchor q)
        (lookup_generation_record_ready (digit_allocated_artifacts q) (\<lambda>u r. {||})) l p c rows queries
      else if m=3 then generation_reading_report
        (\<lambda>u r. digit_generation_fields q None r)
        (\<lambda>G u r. digit_check_generation q G None r)
        (digit_generation_anchor q) (digit_generation_ready q) l p c rows queries
      else if m=4 then generation_reading_report
        (\<lambda>u r. digit_generation_fields q u [])
        (\<lambda>G u r. digit_check_generation q G u [])
        (digit_generation_anchor q) (digit_generation_ready q) l p c rows queries
      else if m=7 then generation_reading_report (digit_generation_fields q)
        (generation_shallow_check (digit_generation_fields q))
        (digit_generation_anchor q) (digit_generation_ready q) l p c rows queries
      else digit_generation_reading_report q l p c rows queries) input)"

definition indexed_generation_mutation ::
  "nat\<Rightarrow>indexed_generation_subject\<Rightarrow>generation_reading_value fset\<Rightarrow>generation_reading_value fset" where
  "indexed_generation_mutation m X results=(if m=13 then {||}
    else if m=14 \<and> fst X=None then {|(False,None,[])|}
    else fimage (\<lambda>(ready,anchors,reads).
      (if m=8 then True else if m=9 then False else ready,
       if m=10 then None else anchors,
       if m=12 then [] else map (\<lambda>(query,read_fields,checked,anchor).
         (query,if m=11 then {||} else read_fields,
          if m=5 then True else if m=6 then False else checked,
          if m=10 then None else anchor)) reads)) results)"

definition indexed_generation_method where
  "indexed_generation_method m X=(if m=1 then indexed_generation_reference X
    else indexed_generation_mutation m X (indexed_generation_variant (indexed_generation_variant_key m) X))"

lemma indexed_generation_correct_methods:
  "m\<in>{0,1} \<Longrightarrow> indexed_generation_method m X=indexed_generation_reference X"
  by (auto simp: indexed_generation_method_def indexed_generation_mutation_def
    indexed_generation_variant_key_def indexed_generation_variant_def indexed_generation_reference_def
    digit_generation_report_exact split: prod.splits option.splits)

definition indexed_generation_context where
  "indexed_generation_context X=(X,indexed_generation_reference X,
    map (\<lambda>k. (k,indexed_generation_variant k X)) [0,2,3,4,7])"

definition indexed_generation_prepared where
  "indexed_generation_prepared m X reference variants=(if m=1 then reference else
    indexed_generation_mutation m X (case map_of variants (indexed_generation_variant_key m) of
      None \<Rightarrow> {||} | Some value \<Rightarrow> value))"

lemma indexed_generation_prepared_exact:
  "indexed_generation_prepared m X (indexed_generation_reference X)
      (map (\<lambda>k. (k,indexed_generation_variant k X)) [0,2,3,4,7])=indexed_generation_method m X"
proof -
  have key: "indexed_generation_variant_key m\<in>set [0,2,3,4,7]"
    by (auto simp: indexed_generation_variant_key_def)
  show ?thesis by (simp only: indexed_generation_prepared_def mapped_function_lookup key
    if_True option.case indexed_generation_method_def)
qed

definition indexed_generation_assessment where
  "indexed_generation_assessment m context=(case context of (X,reference,variants) \<Rightarrow>
    (indexed_generation_prepared m X reference variants,reference))"

definition indexed_generation_inspect :: "(generation_reading_value fset\<times>generation_reading_value fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "indexed_generation_inspect=finite_reader_inspect"

definition indexed_generation_condition where
  "indexed_generation_condition f method X=relation_reader_condition (indexed_generation_relation X) f (method X)"

theorem indexed_generation_assessment_exact:
  "indexed_generation_inspect (indexed_generation_assessment m (indexed_generation_context X)) f=
    indexed_generation_condition f (indexed_generation_method m) X"
  by (simp only: indexed_generation_inspect_def indexed_generation_assessment_def indexed_generation_context_def
    case_prod_conv indexed_generation_prepared_exact indexed_generation_condition_def
    finite_reader_inspect_exact[OF indexed_generation_reference_exact])

text \<open>
  The alternatives execute actual lookup changes or alter complete result
  fields. They expose missing bindings, changed query coordinates, forced truth
  values, omitted recursive predecessor checks, readiness, anchors or fields,
  loss of query results and confusion between unavailable input and a value.
  Shared preparation computes each actual variant once and has an exact
  equation for every subsequent method; no satisfaction values are supplied.
\<close>

end
