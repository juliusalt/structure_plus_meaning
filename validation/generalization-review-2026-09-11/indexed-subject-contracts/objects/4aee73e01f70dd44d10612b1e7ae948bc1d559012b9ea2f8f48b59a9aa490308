theory Factor_Observation_Investigation
  imports Factor_Observation_Results Finite_Investigation_Interface
begin

section \<open>The Same-set presentations are checked alongside a different result\<close>

abbreviation observation_example_facets where
  "observation_example_facets \<equiv> [Payload_Term [0],Payload_Term [2]]"

abbreviation observation_example_rows where
  "observation_example_rows \<equiv>
    [(Payload_Term [0],Payload_Term [4],Payload_Term [1]),
     (Payload_Term [2],Payload_Term [4],Payload_Term [3])]"

abbreviation observation_example_values where
  "observation_example_values \<equiv>
    [Pair_Term (Payload_Term [0]) (Payload_Term [1]),
     Pair_Term (Payload_Term [2]) (Payload_Term [3])]"

definition observation_investigation_output :: "nat \<Rightarrow> factor_term list" where
  "observation_investigation_output c=(if c=0 then observation_example_values
    else if c=1 then rev observation_example_values
    else if c=2 then observation_example_values@[hd observation_example_values]
    else [hd observation_example_values])"

definition observation_investigation_decision :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "observation_investigation_decision f c=(if f=0 then
    (301,context_relation_argument
      (Pair_Term (data_list_term observation_example_facets) (Payload_Term [4]))
      (data_list_term (map observation_row_term observation_example_rows))
      (data_list_term (observation_investigation_output c)))\<in>positive_meaning observation_system
    else (302,context_relation_argument
      (Pair_Term (data_list_term observation_example_facets) (Payload_Term [4]))
      (data_list_term (map observation_row_term observation_example_rows))
      (data_list_term (observation_investigation_output c)))\<in>positive_meaning observation_result_system)"

lemma observation_investigation_decision_code [code]:
  "observation_investigation_decision f c=(if f=0 then c=0 else c<3)"
  by (simp only: observation_investigation_decision_def observation_encoded_profile observation_profile_result_lists)
    (auto simp: observation_investigation_output_def observation_profile_list_def
      data_list_term_injective octets_formed_def)

definition observation_investigation_compare :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "observation_investigation_compare c d \<longleftrightarrow>
    set (observation_investigation_output c)=set (observation_investigation_output d)"

lemma observation_investigation_compare_code [code]:
  "observation_investigation_compare c d \<longleftrightarrow> ((c<3 \<and> d<3) \<or> (3\<le>c \<and> 3\<le>d))"
  by (auto simp: observation_investigation_compare_def observation_investigation_output_def)

definition observation_investigation_observations :: "(nat\<times>nat\<times>nat) list" where
  "observation_investigation_observations=concat (map (\<lambda>c.
    map (\<lambda>f. (f,c,if observation_investigation_decision f c then 1 else 0)) [0,1]) [0,1,2,3])"

definition observation_investigation_relation :: "(nat\<times>nat) list" where
  "observation_investigation_relation=filter (\<lambda>(c,d). observation_investigation_compare c d)
    (investigation_pairs [0,1,2,3])"

lemma observation_investigation_observations_exact:
  "finite_table_observations (fset_of_list observation_investigation_observations) f c=
    (if f\<in>{0,1} \<and> c\<in>{0,1,2,3} then {if observation_investigation_decision f c then 1 else 0} else {})"
  by (cases "f=0"; cases "f=1"; cases "c=0"; cases "c=1"; cases "c=2"; cases "c=3")
    (auto simp: finite_table_observations_def observation_investigation_observations_def
      observation_investigation_decision_code)

lemma observation_investigation_relation_exact:
  "(c,d)\<in>set observation_investigation_relation \<longleftrightarrow>
    c\<in>{0,1,2,3} \<and> d\<in>{0,1,2,3} \<and>
    set (observation_investigation_output c)=set (observation_investigation_output d)"
  by (auto simp: observation_investigation_relation_def investigation_pairs_exact observation_investigation_compare_def)

definition observation_investigation where
  "observation_investigation selected=investigation_basis [0,1,2,3] [0,1] selected
    observation_investigation_observations observation_investigation_relation"

export_code investigation_inference investigation_basis investigation_repairs investigation_extend observation_investigation
  observation_investigation_observations observation_investigation_relation
  nat_of_integer integer_of_nat
  in SML module_name Finite_Investigation file_prefix finite_investigation

text \<open>
  The subjects are the actual ordered, reversed, repeated, and missing-row output lists.
  The independent comparison is equality of their represented sets. One
  observation calls the native ordered profile operation; the other calls
  the new native profile result operation, with its private witness and set comparison. Both
  Boolean outcomes are retained. The report can therefore expose an
  observation that distinguishes presentations of the same intended subject.
\<close>

end
