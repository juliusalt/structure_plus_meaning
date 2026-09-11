theory Factor_Construction_Permission_Examples
  imports Factor_Native_Construction Factor_Pattern_Programs
begin

section \<open>A permission definition that observes an exact account field\<close>

definition construction_output_pattern :: "exact_artifact \<Rightarrow> nat term_pattern" where
  "construction_output_pattern R =
    Pattern_Pair (Pattern_Variable 0)
      (Pattern_Pair (Pattern_Variable 1)
        (Pattern_Pair (Pattern_Variable 2)
          (Pattern_Pair (Pattern_Variable 3)
            (Pattern_Pair (Pattern_Target (Whole_Artifact R))
              (Pattern_Target (Whole_Artifact empty_artifact))))))"

lemma construction_output_pattern_formed:
  assumes "exact_formed R"
  shows "pattern_formed (construction_output_pattern R)"
  using assms by (simp add: construction_output_pattern_def)

lemma construction_output_pattern_accepts:
  assumes rf: "exact_formed R"
  shows "pattern_accepts (construction_output_pattern R) t \<longleftrightarrow>
    (\<exists>a b c v. term_formed a \<and> term_formed b \<and> term_formed c \<and> term_formed v \<and>
      t=enumeration_term [a,b,c,v,Target_Term (Whole_Artifact R)])"
proof
  assume accepts: "pattern_accepts (construction_output_pattern R) t"
  then obtain V where head: "pattern_instance V (construction_output_pattern R) t"
    and tf: "term_formed t" by (auto simp: pattern_accepts_def)
  obtain a b c v where shape: "t=enumeration_term [a,b,c,v,Target_Term (Whole_Artifact R)]"
    using head by (auto simp: construction_output_pattern_def)
  show "\<exists>a b c v. term_formed a \<and> term_formed b \<and> term_formed c \<and> term_formed v \<and>
      t=enumeration_term [a,b,c,v,Target_Term (Whole_Artifact R)]"
    using shape tf by (auto simp: enumeration_term_formed)
next
  assume "\<exists>a b c v. term_formed a \<and> term_formed b \<and> term_formed c \<and> term_formed v \<and>
      t=enumeration_term [a,b,c,v,Target_Term (Whole_Artifact R)]"
  then obtain a b c v where fields: "term_formed a" "term_formed b" "term_formed c" "term_formed v"
    and shape: "t=enumeration_term [a,b,c,v,Target_Term (Whole_Artifact R)]" by blast
  let ?V = "{(0,a),(1,b),(2,c),(3,v)}"
  have bindings: "term_bindings_formed (pattern_variables (construction_output_pattern R)) ?V"
    using fields by (auto simp: term_bindings_formed_def construction_output_pattern_def
      single_valued_def rel_dom_def)
  have head: "pattern_instance ?V (construction_output_pattern R) t"
    using shape rf by (auto simp: construction_output_pattern_def)
  have tf: "term_formed t" using fields rf shape by simp
  show "pattern_accepts (construction_output_pattern R) t"
    using bindings head tf by (auto simp: pattern_accepts_def)
qed

lemma construction_output_meaning:
  assumes expected: "exact_formed S" and built: "source_constructs xs B W R"
    and coords: "construction_coordinates_formed B W"
    and present: "construction_claim_presents xs B W R t"
  shows "((),t)\<in>positive_meaning (recognizer_system 0 (construction_output_pattern S)) \<longleftrightarrow> R=S"
proof -
  have tf: "term_formed t" by (rule construction_claim_presents_formed[OF built coords present])
  show ?thesis
    using recognizer_positive_meaning[OF construction_output_pattern_formed[OF expected], where a=0 and t=t]
      construction_output_pattern_accepts[OF expected, of t] present tf
    by (auto simp: construction_claim_presents_def enumeration_term_formed enumeration_term_injective)
qed

theorem construction_output_permission_invariant:
  assumes expected: "exact_formed S"
  shows "construction_permission_invariant (recognizer_system 0 (construction_output_pattern S)) ()"
  unfolding construction_permission_invariant_def
proof (intro allI impI)
  fix xs B W R t u assume built: "source_constructs xs B W R"
    and coords: "construction_coordinates_formed B W"
    and first: "construction_claim_presents xs B W R t"
    and second: "construction_claim_presents xs B W R u"
  let ?P = "recognizer_system 0 (construction_output_pattern S)"
  have tf: "term_formed t" by (rule construction_claim_presents_formed[OF built coords first])
  have uf: "term_formed u" by (rule construction_claim_presents_formed[OF built coords second])
  show "(schema_call_formed ?P () t \<longleftrightarrow> schema_call_formed ?P () u) \<and>
    (((),t)\<in>positive_meaning ?P \<longleftrightarrow> ((),u)\<in>positive_meaning ?P)"
    using recognizer_call_formed[OF construction_output_pattern_formed[OF expected]]
      construction_output_meaning[OF expected built coords first]
      construction_output_meaning[OF expected built coords second] tf uf by simp
qed

theorem construction_output_permission:
  assumes expected: "exact_formed S"
  shows "factor_constructs (recognizer_system 0 (construction_output_pattern S)) () xs B W R \<longleftrightarrow>
    source_constructs xs B W R \<and> construction_coordinates_formed B W \<and> R=S"
proof (cases "source_constructs xs B W R \<and> construction_coordinates_formed B W")
  case False
  then show ?thesis by (auto simp: factor_constructs_def)
next
  case True
  then have built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W" by auto
  have present: "construction_claim_presents xs B W R (construction_claim_term xs B W R)"
    by (rule construction_claim_term_presents[OF built])
  show ?thesis
    using factor_construction_at_presentation[
      OF built coords construction_output_permission_invariant[OF expected] present]
      construction_output_meaning[OF expected built coords present] True by blast
qed

theorem construction_output_native_program:
  assumes expected: "exact_formed S"
  shows "\<exists>E :: local_address option artifact_environment. \<exists>pu Q d.
    closed_native_package_at E pu [] Q \<and> d\<in>system_definitions Q \<and>
    construction_permission_invariant Q d \<and>
    (\<forall>xs B W R t. source_constructs xs B W R \<longrightarrow>
      construction_coordinates_formed B W \<longrightarrow> construction_claim_presents xs B W R t \<longrightarrow>
      schema_call_formed Q d t \<and> ((d,t)\<in>positive_meaning Q \<longleftrightarrow> R=S))"
proof -
  let ?P = "recognizer_system 0 (construction_output_pattern S)"
  have pf: "schema_system_formed ?P"
    by (rule recognizer_system_formed[OF construction_output_pattern_formed[OF expected]])
  have member: "()\<in>system_definitions ?P"
    by (simp add: system_definitions_def recognizer_system_def rel_dom_def)
  obtain g :: "unit \<Rightarrow> local_address option definition_site" and E pu Q where compiled:
    "inj_on g (system_definitions ?P)" "closed_native_package_at E pu [] Q"
    "system_alpha_variant (rename_system g ?P) Q"
    "positive_meaning Q=image (map_prod g id) (positive_meaning ?P)"
    using program_compilation_total[OF pf] by metis
  have boundary: "\<And>t. schema_call_formed Q (g ()) t \<longleftrightarrow> schema_call_formed ?P () t"
    by (rule compiled_system_call_boundary[OF pf compiled(1,3) member])
  have meaning: "\<And>t. (g (),t)\<in>positive_meaning Q \<longleftrightarrow> ((),t)\<in>positive_meaning ?P"
    by (rule compiled_system_meaning_at[OF compiled(1) member compiled(4)])
  have invariant: "construction_permission_invariant Q (g ())"
    using construction_permission_invariant_transport[OF boundary meaning]
      construction_output_permission_invariant[OF expected] by blast
  have inside: "g ()\<in>system_definitions Q"
    using compiled(3) member
    by (auto simp: system_alpha_variant_def renamed_system_definitions)
  have every: "\<forall>xs B W R t. source_constructs xs B W R \<longrightarrow>
      construction_coordinates_formed B W \<longrightarrow> construction_claim_presents xs B W R t \<longrightarrow>
      schema_call_formed Q (g ()) t \<and> ((g (),t)\<in>positive_meaning Q \<longleftrightarrow> R=S)"
  proof (intro allI impI)
    fix xs B W R t assume built: "source_constructs xs B W R"
      and coords: "construction_coordinates_formed B W"
      and present: "construction_claim_presents xs B W R t"
    have tf: "term_formed t" by (rule construction_claim_presents_formed[OF built coords present])
    show "schema_call_formed Q (g ()) t \<and> ((g (),t)\<in>positive_meaning Q \<longleftrightarrow> R=S)"
      using boundary[of t] meaning[of t] tf construction_output_meaning[OF expected built coords present]
        recognizer_call_formed[OF construction_output_pattern_formed[OF expected], of 0 t] by blast
  qed
  show ?thesis
    by (rule exI[of _ E], rule exI[of _ pu], rule exI[of _ Q], rule exI[of _ "g ()"])
       (use compiled(2) inside invariant every in blast)
qed

text \<open>
  A finite native program can have an unordered construction interface and a
  nonconstant permission: its existing pattern requires exactly the selected
  output artifact. All row orders, including nested atom-set orders, have the
  same interface acceptance and truth. The generic compiler constructs the
  closed package; the native construction theorem supplies every future call.
  This is an example of a policy, not a distinguished foundation permission.
\<close>

end
