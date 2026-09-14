theory Factor_Native_Replay_Correctness
  imports Factor_Native_Replay_Cases
begin

lemma native_replay_base_domain:
  "native_replay_base X\<noteq>None \<longleftrightarrow> native_replay_original X\<noteq>None"
proof -
  obtain E u r p d t where input: "X=(E,u,r,p,d,t)" by (cases X) auto
  have original: "native_replay_original X\<noteq>None \<longleftrightarrow>
    (\<exists>P. finite_native_source E u r=Some P \<and> finite_checks_schema_proof P p d t)"
    by (auto simp: input native_replay_original_def native_replay_reference_def split: option.splits if_splits)
  have produced: "native_replay_base X\<noteq>None \<longleftrightarrow>
    (\<exists>A M root G au I K B. finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B))"
    by (cases "native_replay_base X")
      (auto simp: input native_replay_base_def split: prod.splits)
  show ?thesis by (simp only: original produced finite_native_certificate_replay_domain)
qed

lemma native_replay_constructor_result:
  assumes constructed: "native_replay_base X=Some (A,M,root,G,au,I,K,B)"
    and original: "native_replay_original X=Some P" and facet: "f<9"
  shows "native_replay_result_condition f X P (Some (A,M,root,G,au,I,K,B))"
proof -
  obtain E u r p d t where input: "X=(E,u,r,p,d,t)" by (cases X) auto
  have source: "finite_native_source E u r=Some P"
    using original by (simp only: input native_replay_original_exact finite_native_source_correct; blast)
  have result: "finite_native_certificate_replay E u r p d t=Some (A,M,root,G,au,I,K,B)"
    using constructed by (simp only: input native_replay_base_def case_prod_conv)
  have facts:
    "finite_environment_formed A"
    "environment_included (decode_finite_environment E) (decode_finite_environment A)"
    "finite_environment_agrees_on E A (finite_environment_uses E)"
    "finite_native_source A u r=Some P"
    "finite_graph_mapping M (finite_source_proof_graph P (p,d,t)) (p,d,t) G root"
    "single_valued ((fset M)\<inverse>)"
    "G |\<in>| finite_native_graph_readings A root"
    "((d,t),I,K) |\<in>| finite_application_readings A au []"
    "B=finite_native_replay_environment A u r au [] G"
    "finite_environment_formed B"
    "environment_included (decode_finite_environment B) (decode_finite_environment A)"
    "P |\<in>| finite_native_package_readings B u r"
    "G |\<in>| finite_native_graph_readings B root"
    "((d,t),I,K) |\<in>| finite_application_readings B au []"
    "{||} |\<in>| finite_native_replay_readings B u r au [] root"
    "image fst (fset (finite_graph_nodes G))\<inter>fset (finite_environment_uses E)={}"
    by (rule finite_native_certificate_replay_correct[OF result source])+
  have graph: "finite_native_graph_result_condition f E (finite_source_proof_graph P (p,d,t))
    (p,d,t) (Some (A,M,root,G))" if "f<5"
    by (rule finite_native_graph_result_conditions[OF facts(1) facts(7) facts(5) facts(2) facts(3)
      facts(16) facts(6) that])
  show ?thesis using facts(4,8,9,10,11,12,13,14,15) graph facet
    by (auto simp: input native_replay_result_condition_def finite_native_source_correct
      finite_application_readings_correct finite_native_replay_environment_correct[symmetric]
      finite_environment_formed_correct finite_native_package_readings_correct
      finite_native_graph_readings_correct finite_native_replay_readings_correct; arith)
qed

theorem native_replay_constructor_all_conditions:
  assumes facet: "f<10"
  shows "native_replay_condition f (native_replay_method 0) X"
proof (cases "native_replay_original X")
  case None
  have missing: "native_replay_base X=None" using None native_replay_base_domain[of X] by blast
  show ?thesis using facet
    by (auto simp: native_replay_condition_def native_replay_method_original None missing Let_def; arith)
next
  case (Some P)
  have present: "native_replay_base X\<noteq>None" using Some native_replay_base_domain[of X] by blast
  obtain z where found: "native_replay_base X=Some z" using present by (cases "native_replay_base X") auto
  obtain A M root G au I K B where shape: "z=(A,M,root,G,au,I,K,B)" by (cases z) auto
  have result: "native_replay_base X=Some (A,M,root,G,au,I,K,B)" using found by (simp only: shape)
  have body: "native_replay_result_condition k X P (Some (A,M,root,G,au,I,K,B))" if "k<9" for k
    by (rule native_replay_constructor_result[OF result Some that])
  show ?thesis using facet body
    by (auto simp: native_replay_condition_def native_replay_method_original Some result Let_def; arith)
qed

end
