theory Factor_Proof_Claim_Instances
  imports Factor_Proof_Claim_Values
begin

section \<open>Actual node metadata fixes the claim's branch\<close>

lemma native_graph_read_node:
  assumes graph: "native_schema_graph_at E root G" and member: "n\<in>schema_graph_nodes G"
    and raw: "native_proof_node_at E (fst n) (snd n) N D I K"
  shows "(n,N)\<in>fset (graph_inferences G)" "D=schema_graph_premises G n"
proof -
  obtain A J W where actual: "(n,A)\<in>fset (graph_inferences G)"
    "native_proof_node_at E (fst n) (snd n) A (schema_graph_premises G n) J W"
    using native_schema_graph_node[OF graph member] by blast
  have same: "N=A \<and> D=schema_graph_premises G n" using native_proof_node_unique[OF raw actual(2)] by blast
  show "(n,N)\<in>fset (graph_inferences G)" "D=schema_graph_premises G n" using actual(1) same by simp_all
qed

lemma schema_graph_inference_not_assertion:
  assumes formed: "schema_graph_formed G root" and node: "(n,Schema_Inference c V)\<in>fset (graph_inferences G)"
  shows "(n,Schema_Assertion)\<notin>fset (graph_inferences G)"
proof
  assume assertion: "(n,Schema_Assertion)\<in>fset (graph_inferences G)"
  have functional: "single_valued (fset (graph_inferences G))" using formed by (simp add: schema_graph_formed_def)
  have same: "Schema_Inference c V=Schema_Assertion" by (rule single_valued_outputs[OF functional node assertion])
  then show False by simp
qed

lemma proof_node_inference_fields:
  assumes source: "environment_value_presents E e"
    and read: "(94,term_quotation_argument e (use_data_term u) (Payload_Term r)
      (data_list_term [definition_site_value c,positioned_binding_rows_term vs,z]) i k)
      \<in>positive_meaning proof_node_reading_system"
  obtains ds I K where "z=discharge_rows_term ds" "distinct vs" "distinct ds"
    "native_proof_node_at E u r (Schema_Inference c (fset_of_list vs)) (set ds) I K"
proof -
  obtain N D Is Ks where presented: "proof_node_value_presents N D
      (data_list_term [definition_site_value c,positioned_binding_rows_term vs,z])"
    and raw: "native_proof_node_at E u r N D (set Is) (set Ks)"
    using read by (simp only: proof_node_reading_at_source[OF source] inj_eq[OF use_data_term_injective]
      factor_term.inject; blast)
  obtain a V bs ds where fields:
    "N=Schema_Inference a V" "z=discharge_rows_term ds"
    using presented by (cases N) auto
  have exact: "distinct vs \<and> distinct ds \<and> N=Schema_Inference c (fset_of_list vs) \<and> D=set ds"
    using presented by (simp only: fields(2) proof_node_value_inference)
  show thesis by (rule that[OF fields(2)]) (use exact raw in auto)
qed

lemma proof_claim_at_assertion:
  assumes formed: "schema_graph_formed G root" and node: "(n,Schema_Assertion)\<in>fset (graph_inferences G)"
  shows "proof_claim_at P G js n d t \<longleftrightarrow>
    schema_call_formed P d t \<and> schema_graph_premises G n={}"
proof -
  have sv: "single_valued (fset (graph_inferences G))" using formed by (simp add: schema_graph_formed_def)
  have absent: "(n,Schema_Inference c V)\<notin>fset (graph_inferences G)" for c V
    using single_valued_outputs[OF sv node] by auto
  show ?thesis by (simp add: proof_claim_at_def node absent)
qed

lemma proof_claim_at_inference:
  assumes formed: "schema_graph_formed G root" and node: "(n,Schema_Inference c V)\<in>fset (graph_inferences G)"
  shows "proof_claim_at P G js n d t \<longleftrightarrow>
    (\<exists>Q. admitted_schema_instance P d c (fset V) t Q \<and>
      rel_dom (schema_graph_premises G n)=rel_dom Q \<and>
      (\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
        key_values (definition_site_value m) js=
          [call_instance_value (fst (rel_value Q s)) (snd (rel_value Q s))]))"
proof -
  have sv: "single_valued (fset (graph_inferences G))" using formed by (simp add: schema_graph_formed_def)
  have same: "(n,A)\<in>fset (graph_inferences G) \<longleftrightarrow> A=Schema_Inference c V" for A
    using node single_valued_outputs[OF sv node] by blast
  show ?thesis by (simp only: proof_claim_at_def same inference_node.distinct inference_node.inject; blast)
qed

section \<open>The ordinary row join is exactly the complete premise boundary\<close>

lemma positioned_join_rows:
  assumes joined: "keyed_row_join (pair_list_term js) (encoded_discharge_rows ds) (encoded_positioned_calls qs)"
  shows "(\<forall>s m. (s,m)\<in>set ds \<longrightarrow>
      (\<exists>d t. (s,d,t)\<in>set qs \<and> key_values (definition_site_value m) js=[call_instance_value d t])) \<and>
    (\<forall>s d t. (s,d,t)\<in>set qs \<longrightarrow>
      (\<exists>m. (s,m)\<in>set ds \<and> key_values (definition_site_value m) js=[call_instance_value d t]))"
proof -
  have entries: "\<forall>s n. (s,n)\<in>set (encoded_discharge_rows ds) \<longrightarrow>
      (\<exists>v. (s,v)\<in>set (encoded_positioned_calls qs) \<and> key_values n js=[v])"
    "\<forall>s v. (s,v)\<in>set (encoded_positioned_calls qs) \<longrightarrow>
      (\<exists>n. (s,n)\<in>set (encoded_discharge_rows ds) \<and> key_values n js=[v])"
    using keyed_row_join_entries[OF joined] by blast+
  have forward: "\<exists>d t. (s,d,t)\<in>set qs \<and>
      key_values (definition_site_value m) js=[call_instance_value d t]"
    if row: "(s,m)\<in>set ds" for s m
  proof -
    have encoded: "(definition_site_value s,definition_site_value m)\<in>set (encoded_discharge_rows ds)"
      using row by auto
    obtain v where row_value: "(definition_site_value s,v)\<in>set (encoded_positioned_calls qs)"
      "key_values (definition_site_value m) js=[v]" using entries(1) encoded by blast
    obtain z where actual: "z\<in>set qs"
      and image: "(definition_site_value s,v)=(case z of (a,d,t) \<Rightarrow> (definition_site_value a,call_instance_value d t))"
      using row_value(1) by (simp only: set_map; blast)
    obtain a d t where z: "z=(a,d,t)" by (cases z) auto
    have decoded: "a=s" "v=call_instance_value d t"
      using image by (simp only: z case_prod_conv prod.inject definition_site_value_eq; blast)+
    have row: "(s,d,t)\<in>set qs" using actual z decoded(1) by simp
    show ?thesis by (rule exI[of _ d], rule exI[of _ t]) (use row row_value(2) decoded(2) in simp)
  qed
  have backward: "\<exists>m. (s,m)\<in>set ds \<and>
      key_values (definition_site_value m) js=[call_instance_value d t]"
    if row: "(s,d,t)\<in>set qs" for s d t
  proof -
    have encoded: "(definition_site_value s,call_instance_value d t)\<in>set (encoded_positioned_calls qs)"
      by (simp only: set_map; rule image_eqI[OF _ row]) simp
    obtain n where row_value: "(definition_site_value s,n)\<in>set (encoded_discharge_rows ds)"
      "key_values n js=[call_instance_value d t]" using entries(2) encoded by blast
    obtain z where actual: "z\<in>set ds"
      and image: "(definition_site_value s,n)=(case z of (a,m) \<Rightarrow> (definition_site_value a,definition_site_value m))"
      using row_value(1) by (simp only: set_map; blast)
    obtain a m where z: "z=(a,m)" by (cases z)
    have decoded: "a=s" "n=definition_site_value m"
      using image by (simp only: z case_prod_conv prod.inject definition_site_value_eq; blast)+
    have row: "(s,m)\<in>set ds" using actual z decoded(1) by simp
    show ?thesis by (rule exI[of _ m]) (use row row_value(2) decoded(2) in simp)
  qed
  show ?thesis using forward backward by blast
qed

lemma positioned_join_claim:
  assumes node: "(n,Schema_Inference c V)\<in>fset (graph_inferences G)"
    and admitted: "admitted_schema_instance P d c (fset V) t (set qs)"
    and premise_rows: "set ds=schema_graph_premises G n"
    and joined: "keyed_row_join (pair_list_term js) (encoded_discharge_rows ds) (encoded_positioned_calls qs)"
  shows "proof_claim_at P G js n d t"
proof -
  have rows: "(\<forall>s m. (s,m)\<in>set ds \<longrightarrow>
      (\<exists>e x. (s,e,x)\<in>set qs \<and> key_values (definition_site_value m) js=[call_instance_value e x])) \<and>
    (\<forall>s e x. (s,e,x)\<in>set qs \<longrightarrow>
      (\<exists>m. (s,m)\<in>set ds \<and> key_values (definition_site_value m) js=[call_instance_value e x]))"
    by (rule positioned_join_rows[OF joined])
  have list_domains: "rel_dom (set ds)=rel_dom (set qs)"
  proof (rule set_eqI)
    fix s :: "local_address option definition_site"
    show "s\<in>rel_dom (set ds) \<longleftrightarrow> s\<in>rel_dom (set qs)"
    proof
      assume "s\<in>rel_dom (set ds)"
      then obtain m where row: "(s,m)\<in>set ds" unfolding rel_dom_def by blast
      obtain e x where target: "(s,e,x)\<in>set qs" using rows row by blast
      show "s\<in>rel_dom (set qs)" by (rule rel_domI[OF target])
    next
      assume "s\<in>rel_dom (set qs)"
      then obtain q where target: "(s,q)\<in>set qs" unfolding rel_dom_def by blast
      obtain e x where q: "q=(e,x)" by (cases q)
      have actual: "(s,e,x)\<in>set qs" using target q by simp
      obtain m where row: "(s,m)\<in>set ds" using rows actual by blast
      show "s\<in>rel_dom (set ds)" by (rule rel_domI[OF row])
    qed
  qed
  have domain: "rel_dom (schema_graph_premises G n)=rel_dom (set qs)"
    using list_domains premise_rows by simp
  have sv: "single_valued (set qs)" using admitted_instance_formed[OF admitted] by blast
  have fibres: "key_values (definition_site_value m) js=
      [call_instance_value (fst (rel_value (set qs) s)) (snd (rel_value (set qs) s))]"
    if premise: "(s,m)\<in>schema_graph_premises G n" for s m
  proof -
    obtain e x where row_value: "(s,e,x)\<in>set qs"
      "key_values (definition_site_value m) js=[call_instance_value e x]"
      using rows premise premise_rows by blast
    have actual: "rel_value (set qs) s=(e,x)" by (rule rel_value_eq[OF sv row_value(1)])
    show ?thesis using row_value(2) by (simp only: actual fst_conv snd_conv)
  qed
  show ?thesis unfolding proof_claim_at_def
    by (intro disjI2, rule exI[of _ c], rule exI[of _ V], rule exI[of _ "set qs"])
      (use node admitted domain fibres in blast)
qed

lemma relation_rows_at_keys:
  fixes Q :: "('s\<times>'v) set" and ds :: "('s\<times>'n) list"
  assumes sv: "single_valued Q" and domain: "rel_dom (set ds)=rel_dom Q"
  shows "set (map (\<lambda>(s,m). (s,rel_value Q s)) ds)=Q"
proof (rule set_eqI)
  fix z :: "'s\<times>'v"
  obtain s q where shape: "z=(s,q)" by (cases z)
  show "z\<in>set (map (\<lambda>(s,m). (s,rel_value Q s)) ds) \<longleftrightarrow> z\<in>Q"
  proof
    assume selected: "z\<in>set (map (\<lambda>(s,m). (s,rel_value Q s)) ds)"
    obtain m where row: "(s,m)\<in>set ds" and q: "q=rel_value Q s"
      using selected by (auto simp: shape)
    have key: "s\<in>rel_dom Q" using rel_domI[OF row] by (simp only: domain)
    obtain v where actual: "(s,v)\<in>Q" using key unfolding rel_dom_def by blast
    have rv: "rel_value Q s=v" by (rule rel_value_eq[OF sv actual])
    show "z\<in>Q" using actual q rv shape by simp
  next
    assume selected: "z\<in>Q"
    have actual: "(s,q)\<in>Q" using selected shape by simp
    have key: "s\<in>rel_dom (set ds)" using rel_domI[OF actual] domain by simp
    obtain m where row: "(s,m)\<in>set ds" using key unfolding rel_dom_def by blast
    have rv: "rel_value Q s=q" by (rule rel_value_eq[OF sv actual])
    show "z\<in>set (map (\<lambda>(s,m). (s,rel_value Q s)) ds)"
      by (simp only: set_map; rule image_eqI[OF _ row]) (simp add: shape rv)
  qed
qed

lemma owned_rows_recover:
  assumes owner: "\<And>s q. (s,q)\<in>set ps \<Longrightarrow> fst s=u"
  shows "map (\<lambda>(s,q). ((u,s),q)) (map (\<lambda>(s,q). (snd s,q)) ps)=ps"
  using owner
proof (induction ps)
  case Nil
  then show ?case by simp
next
  case (Cons row ps)
  obtain s q where row: "row=(s,q)" by (cases row)
  have first: "fst s=u" by (rule Cons.prems[of s q]) (simp add: row)
  have tail_owner: "fst a=u" if "(a,v)\<in>set ps" for a v
    by (rule Cons.prems[of a v]) (use that in simp)
  have tail: "map (\<lambda>(s,q). ((u,s),q)) (map (\<lambda>(s,q). (snd s,q)) ps)=ps"
    by (rule Cons.IH[OF tail_owner])
  show ?case using first tail by (cases s) (simp add: row)
qed

section \<open>Every valid inference supplies the ordinary checking operands\<close>

lemma native_inference_claim_operands:
  assumes source: "environment_value_presents E e" and package: "native_package_at E pu pr P"
    and graph: "native_schema_graph_at E root G" and node: "(n,Schema_Inference c V)\<in>fset (graph_inferences G)"
    and rows: "formed_key_rows js" and claim: "proof_claim_at (positioned_program P) G js n d t"
  obtains a bs vs ds qs ps i k where
    "c=(fst d,a)"
    "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n))
      (data_list_term [definition_site_value c,positioned_binding_rows_term vs,discharge_rows_term ds]) i k)
      \<in>positive_meaning proof_node_reading_system"
    "(99,row_qualification_argument (use_data_term (fst d)) (binding_rows_term bs) (positioned_binding_rows_term vs))
      \<in>positive_meaning row_qualification_system"
    "(100,keyed_row_join_argument (pair_list_term js) (discharge_rows_term ds) (positioned_call_rows_term ps))
      \<in>positive_meaning keyed_row_join_system"
    "(99,row_qualification_argument (use_data_term (fst d)) (call_instance_rows_term qs) (positioned_call_rows_term ps))
      \<in>positive_meaning row_qualification_system"
    "(87,admitted_instantiation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d)
      (Payload_Term a) (binding_rows_term bs) t (call_instance_rows_term qs))\<in>positive_meaning admitted_instantiation_system"
proof -
  have gf: "schema_graph_formed G root" using graph by (simp add: native_schema_graph_at_def)
  have pf: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  obtain Q where admitted: "admitted_schema_instance (positioned_program P) d c (fset V) t Q"
    and domain: "rel_dom (schema_graph_premises G n)=rel_dom Q"
    and fibres: "\<forall>s m. (s,m)\<in>schema_graph_premises G n \<longrightarrow>
      key_values (definition_site_value m) js=[call_instance_value (fst (rel_value Q s)) (snd (rel_value Q s))]"
    using claim by (simp only: proof_claim_at_inference[OF gf node]; blast)
  obtain a B R where original: "c=(fst d,a)" "fset V=rename_term_bindings (Pair (fst d)) B"
    "Q=map_socket_graph (Pair (fst d)) id id R" "admitted_schema_instance P d a B t R"
    by (rule positioned_admitted_instanceE[OF pf admitted]) (rule that; assumption)
  have bfinite: "finite B"
    using original(4) by (auto simp: admitted_schema_instance_def schema_instance_def term_bindings_formed_def)
  obtain bs where bindings: "set bs=B" "distinct bs" using finite_distinct_list[OF bfinite] by blast
  let ?vs="map (\<lambda>(a,t). ((fst d,a),t)) bs"
  have vs: "set ?vs=fset V" "distinct ?vs"
    using original(2) bindings by (auto simp: rename_term_bindings_def distinct_map inj_on_def)
  obtain I K where raw: "native_proof_node_at E (fst n) (snd n) (Schema_Inference c V) (schema_graph_premises G n) I K"
    using native_schema_graph_entry[OF graph node] by blast
  obtain ds where discharges: "set ds=schema_graph_premises G n" "distinct ds"
    using finite_distinct_list[of "schema_graph_premises G n"] by auto
  have dkeys: "distinct (map fst ds)"
    using discharges schema_graph_premises_functional[OF gf, of n] by (simp add: distinct_keys_iff)
  have qsv: "single_valued Q" using admitted_instance_formed[OF admitted] by blast
  let ?ps="map (\<lambda>(s,m). (s,rel_value Q s)) ds"
  have ps: "set ?ps=Q" by (rule relation_rows_at_keys[OF qsv]) (simp add: discharges(1) domain)
  have pkeys: "distinct (map fst ?ps)" using dkeys by (simp add: comp_def case_prod_unfold)
  have porder: "distinct ?ps" using pkeys by (simp only: distinct_keys_iff; blast)
  have owner: "fst s=fst d" if "(s,q)\<in>Q" for s q
    using that original(3) by (auto simp: map_socket_graph_def)
  let ?qs="map (\<lambda>(s,q). (snd s,q)) ?ps"
  have restored: "map (\<lambda>(s,q). ((fst d,s),q)) ?qs=?ps"
    by (rule owned_rows_recover) (use owner ps in blast)
  have lowered: "(\<lambda>(s,q). (snd s,q)) ` Q=R"
    by (simp add: original(3) map_socket_graph_def map_prod_def image_image comp_def case_prod_unfold)
  have qset: "set ?qs=R"
  proof -
    have "set ?qs=(\<lambda>(s,q). (snd s,q)) ` set ?ps" by (rule set_map)
    also have "...=(\<lambda>(s,q). (snd s,q)) ` Q" by (simp only: ps)
    also have "...=R" by (rule lowered)
    finally show ?thesis .
  qed
  have qualified_order: "distinct (map (\<lambda>(s,q). ((fst d,s),q)) ?qs)"
    by (simp only: restored; rule porder)
  have qorder: "distinct ?qs" by (rule conjunct1[OF iffD1[OF distinct_map qualified_order]])
  have inst: "admitted_schema_instance P d a (set bs) t (set ?qs)" using original(4) bindings(1) qset by simp
  have ordinary: "(87,admitted_instantiation_argument e (use_data_term pu) (Payload_Term pr) (definition_site_value d)
      (Payload_Term a) (binding_rows_term bs) t (call_instance_rows_term ?qs))\<in>positive_meaning admitted_instantiation_system"
    by (rule admitted_instantiation_complete[OF source package bindings(2) qorder inst])
  have formed: "term_formed (use_data_term (fst d))" "term_formed (binding_rows_term bs)"
    "term_formed (call_instance_rows_term ?qs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF ordinary]] by auto
  have binding_qualification: "(99,row_qualification_argument (use_data_term (fst d))
      (binding_rows_term bs) (positioned_binding_rows_term ?vs))\<in>positive_meaning row_qualification_system"
    using row_qualification_complete[OF formed(1,2)] by (simp only: qualify_binding_rows)
  have premise_qualification: "(99,row_qualification_argument (use_data_term (fst d))
      (call_instance_rows_term ?qs) (positioned_call_rows_term ?ps))\<in>positive_meaning row_qualification_system"
    using row_qualification_complete[OF formed(1), of "map (\<lambda>(s,d,t). (Payload_Term s,call_instance_value d t)) ?qs"]
      formed(3) by (simp only: local_call_rows_encoding[symmetric] qualify_call_rows restored)
  have key_formation: "\<forall>s m. (s,m)\<in>set ds \<longrightarrow>
      term_formed (definition_site_value s) \<and> term_formed (definition_site_value m) \<and>
      self_contained_term (definition_site_value m) \<and>
      key_values (definition_site_value m) js=[call_instance_value (fst (rel_value Q s)) (snd (rel_value Q s))]"
    using native_discharge_values_formed[OF raw, of ds] discharges(1) fibres by auto
  have joined: "keyed_row_join (pair_list_term js) (encoded_discharge_rows ds) (encoded_positioned_calls ?ps)"
    using keyed_row_join_mapped[OF rows, where key=definition_site_value and target=definition_site_value
      and f="rel_value Q" and val="\<lambda>(d,t). call_instance_value d t"] key_formation
    by (simp add: comp_def case_prod_unfold)
  have join: "(100,keyed_row_join_argument (pair_list_term js) (discharge_rows_term ds) (positioned_call_rows_term ?ps))
      \<in>positive_meaning keyed_row_join_system"
    by (rule keyed_row_join_complete[OF pair_list_term_formed[OF rows] joined])
  have presented: "proof_node_value_presents (Schema_Inference c V) (schema_graph_premises G n)
      (data_list_term [definition_site_value c,positioned_binding_rows_term ?vs,discharge_rows_term ds])"
    by (simp only: proof_node_value_presents.simps, rule exI[of _ ?vs], rule exI[of _ ds])
      (use vs discharges in simp)
  obtain i k where read: "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n))
      (data_list_term [definition_site_value c,positioned_binding_rows_term ?vs,discharge_rows_term ds]) i k)
      \<in>positive_meaning proof_node_reading_system"
    using proof_node_reading_value[OF source raw presented] by blast
  show thesis by (rule that[OF original(1) read binding_qualification join premise_qualification ordinary])
qed

text \<open>
  Native node uniqueness fixes assertion versus inference and recovers the
  entire premise relation. An inference's admitted positioned instance is
  recovered as an actual local package instance with the same binding values.
  Its premise rows follow an enumeration of the actual links and qualify
  back to the exact supplied socket sites.

  The child table is read through complete singleton fibres. The resulting
  relation has precisely the required socket domain and call at every socket,
  including when different sockets refer to one shared child.
\<close>

end
