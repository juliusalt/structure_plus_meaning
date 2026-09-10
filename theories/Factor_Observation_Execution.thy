theory Factor_Observation_Execution
  imports Factor_Observation_Contracts "HOL-Library.Code_Target_Nat"
begin

section \<open>Injective changes preserve the list computations\<close>

lemma observation_profile_list_map:
  assumes "inj a" "inj b"
  shows "observation_profile_list (map a F) (map (\<lambda>(f,d,w). (a f,b d,e w)) rows) (b c)=
    map (\<lambda>(f,w). (a f,e w)) (observation_profile_list F rows c)"
  using assms by (induction rows)
    (auto simp: observation_profile_list_def inj_image_mem_iff inj_eq split: prod.splits)

lemma observation_losses_list_map:
  assumes "inj a" "inj b" "inj e"
  shows "observation_losses_list (map a F) (map (\<lambda>(f,d,w). (a f,b d,e w)) rows) (b c) (b d)=
    map (\<lambda>(f,w). (a f,e w)) (observation_losses_list F rows c d)"
proof -
  have injective: "inj (\<lambda>(f,w). (a f,e w))"
    using assms by (auto simp: inj_on_def split: prod.splits)
  show ?thesis
    by (simp only: observation_losses_list_def observation_profile_list_map[OF assms(1,2)]
      filter_map comp_def set_map inj_image_mem_iff[OF injective])
qed

section \<open>Executed equations refer to the actual fixed native operations\<close>

abbreviation observation_octet :: "nat \<Rightarrow> factor_term" where
  "observation_octet n \<equiv> Payload_Term [n]"

abbreviation observation_octet_row where
  "observation_octet_row z \<equiv> case z of (f,c,w) \<Rightarrow>
    (observation_octet f,observation_octet c,observation_octet w)"

abbreviation observation_octet_value where
  "observation_octet_value z \<equiv> case z of (f,w) \<Rightarrow> (observation_octet f,observation_octet w)"

lemma observation_octet_injective: "inj observation_octet"
  by (auto simp: inj_on_def)

lemma observation_octet_value_injective:
  "inj (\<lambda>z. observation_value_term (observation_octet_value z))"
  by (auto simp: inj_on_def split: prod.splits)

definition observation_octet_profile :: "nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow>
    nat \<Rightarrow> (nat\<times>nat) list \<Rightarrow> bool" where
  "observation_octet_profile F rows c displayed \<longleftrightarrow>
    (302,context_relation_argument (Pair_Term (data_list_term (map observation_octet F)) (observation_octet c))
      (data_list_term (map observation_row_term (map observation_octet_row rows)))
      (data_list_term (map observation_value_term (map observation_octet_value displayed))))
      \<in>positive_meaning observation_result_system"

definition observation_octet_losses :: "nat list \<Rightarrow> (nat\<times>nat\<times>nat) list \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> (nat\<times>nat) list \<Rightarrow> bool" where
  "observation_octet_losses F rows c d displayed \<longleftrightarrow>
    (307,context_relation_argument (Pair_Term (data_list_term (map observation_octet F))
      (Pair_Term (observation_octet c) (observation_octet d)))
      (data_list_term (map observation_row_term (map observation_octet_row rows)))
      (data_list_term (map observation_value_term (map observation_octet_value displayed))))
      \<in>positive_meaning observation_result_system"

lemma observation_octet_profile_code [code]:
  "observation_octet_profile F rows c displayed \<longleftrightarrow>
    list_all (\<lambda>f. f<256) F \<and> c<256 \<and>
    list_all (\<lambda>(f,d,w). f<256 \<and> d<256 \<and> w<256) rows \<and>
    list_all (\<lambda>(f,w). f<256 \<and> w<256) displayed \<and>
    set displayed=set (observation_profile_list F rows c)"
  unfolding observation_octet_profile_def
  apply (subst observation_profile_result_lists)
  apply (simp only:
      observation_profile_list_map[OF observation_octet_injective observation_octet_injective]
      map_map comp_def set_map inj_image_eq_iff[OF observation_octet_value_injective])
  by (auto simp: list_all_iff octets_formed_def split: prod.splits)

lemma observation_octet_losses_code [code]:
  "observation_octet_losses F rows c d displayed \<longleftrightarrow>
    list_all (\<lambda>f. f<256) F \<and> c<256 \<and> d<256 \<and>
    list_all (\<lambda>(f,e,w). f<256 \<and> e<256 \<and> w<256) rows \<and>
    list_all (\<lambda>(f,w). f<256 \<and> w<256) displayed \<and>
    set displayed=set (observation_losses_list F rows c d)"
  unfolding observation_octet_losses_def
  apply (subst observation_losses_result_lists)
  apply (simp only:
      observation_losses_list_map[OF observation_octet_injective observation_octet_injective observation_octet_injective]
      map_map comp_def set_map inj_image_eq_iff[OF observation_octet_value_injective])
  by (auto simp: list_all_iff octets_formed_def split: prod.splits)

section \<open>Formed references still lie outside the data input boundary\<close>

abbreviation observation_reference where
  "observation_reference \<equiv> Target_Term (Whole_Artifact empty_artifact)"

abbreviation observation_reference_facets where
  "observation_reference_facets n \<equiv> if n=3 then [observation_reference] else []"

abbreviation observation_reference_candidate where
  "observation_reference_candidate n \<equiv> if n=4 then observation_reference else Payload_Term []"

abbreviation observation_reference_rows where
  "observation_reference_rows n \<equiv> if n<3 then
    [(if n=0 then observation_reference else Payload_Term [],
      if n=1 then observation_reference else Payload_Term [],
      if n=2 then observation_reference else Payload_Term [])] else []"

abbreviation observation_reference_profile_argument where
  "observation_reference_profile_argument n \<equiv>
    context_relation_argument
      (Pair_Term (data_list_term (observation_reference_facets n)) (observation_reference_candidate n))
      (data_list_term (map observation_row_term (observation_reference_rows n))) (data_list_term [])"

lemma observation_reference_profile_formed:
  "schema_call_formed observation_result_system 302 (observation_reference_profile_argument n)"
  by (simp add: observation_result_call data_list_term_formed octets_formed_def split: if_splits)

definition observation_reference_profile_decision :: "nat \<Rightarrow> bool" where
  "observation_reference_profile_decision n \<longleftrightarrow>
    (302,observation_reference_profile_argument n)\<in>positive_meaning observation_result_system"

lemma observation_reference_profile_decision_code [code]:
  "observation_reference_profile_decision n \<longleftrightarrow> 5\<le>n"
  unfolding observation_reference_profile_decision_def
  by (subst observation_profile_result_lists)
    (auto simp: observation_profile_list_def octets_formed_def split: if_splits)

abbreviation observation_reference_losses_argument where
  "observation_reference_losses_argument bad \<equiv>
    context_relation_argument (Pair_Term (data_list_term [])
      (Pair_Term (Payload_Term []) (if bad then observation_reference else Payload_Term [])))
      (data_list_term (map observation_row_term [])) (data_list_term [])"

lemma observation_reference_losses_formed:
  "schema_call_formed observation_result_system 307 (observation_reference_losses_argument bad)"
  by (simp add: observation_result_call data_list_term_formed octets_formed_def)

definition observation_reference_losses_decision :: "bool \<Rightarrow> bool" where
  "observation_reference_losses_decision bad \<longleftrightarrow>
    (307,observation_reference_losses_argument bad)\<in>positive_meaning observation_result_system"

lemma observation_reference_losses_decision_code [code]:
  "observation_reference_losses_decision bad \<longleftrightarrow> \<not>bad"
  unfolding observation_reference_losses_decision_def
  by (subst observation_losses_result_lists)
    (simp add: observation_losses_list_def observation_profile_list_def octets_formed_def)

export_code observation_octet_profile observation_octet_losses
  observation_reference_profile_decision observation_reference_losses_decision nat_of_integer integer_of_nat
  in SML module_name Native_Observation file_prefix native_observation

text \<open>
  Each exported decision is defined by the actual native call. The proved
  code equations retain the full octet boundary of every supplied operand.
  They support finite execution checks of these fixed operations. Their
  octet presentation is one testing interface; the preceding contracts cover
  arbitrary admitted data terms and all finite-set list presentations.
\<close>

end
