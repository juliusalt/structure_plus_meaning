theory Factor_Proof_Bound_Values
  imports Factor_Proof_Link_Checking Factor_Proof_Graph_Bounds
begin

section \<open>Complete node values and the origins recovered from their links\<close>

abbreviation proof_bound_term where
  "proof_bound_term bs \<equiv> keyed_rows_term definition_site_value id bs"

abbreviation encoded_discharge_rows where
  "encoded_discharge_rows ds \<equiv> map (\<lambda>(s,n). (definition_site_value s,definition_site_value n)) ds"

abbreviation origin_entry where
  "origin_entry z \<equiv> (definition_site_value (fst z),
    Pair_Term (definition_site_value (fst (snd z))) (definition_site_value (snd (snd z))))"

abbreviation native_value_rows ::
  "local_address option artifact_environment \<Rightarrow>
    (local_address option definition_site\<times>factor_term) list \<Rightarrow> bool" where
  "native_value_rows E bs \<equiv> \<forall>(n,t)\<in>set bs. \<exists>N D I K.
    proof_node_value_presents N D t \<and> native_proof_node_at E (fst n) (snd n) N D I K"

abbreviation proof_value_links where
  "proof_value_links t ds \<equiv> (t=Payload_Term [] \<and> ds=[]) \<or>
    (\<exists>c vs. t=data_list_term [definition_site_value c,positioned_binding_rows_term vs,discharge_rows_term ds])"

definition native_link_origins where
  "native_link_origins E p ds =
    map (\<lambda>(s,n). origin_entry (n,(p,s)))
      (filter (\<lambda>(s,n). \<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K) ds)"

lemma origin_entry_injective: "inj origin_entry"
  by (rule injI) (auto simp: definition_site_value_eq)

lemma proof_value_links_unique:
  assumes "proof_value_links t ds" "proof_value_links t es"
  shows "ds=es"
  using assms
  by (auto simp only: data_list_term.simps factor_term.inject factor_term.distinct
    discharge_rows_term_injective; blast)

lemma proof_node_value_links:
  assumes presented: "proof_node_value_presents N D t"
  shows "\<exists>ds. proof_value_links t ds \<and> distinct ds \<and> set ds=D"
  using presented by (cases N) auto

lemma proof_node_reading_value:
  assumes source: "environment_value_presents E e"
    and raw: "native_proof_node_at E u r N D I K" and presented: "proof_node_value_presents N D t"
  shows "\<exists>i k. (94,term_quotation_argument e (use_data_term u) (Payload_Term r) t i k)
    \<in>positive_meaning proof_node_reading_system"
proof -
  obtain Is where interior: "distinct Is" "set Is=I"
    using finite_distinct_list[OF native_proof_node_properties(6)[OF raw]] by blast
  obtain Ks where slots: "distinct Ks" "set Ks=K"
    using finite_distinct_list[OF native_proof_node_properties(7)[OF raw]] by blast
  have at: "native_proof_node_at E u r N D (set Is) (set Ks)" using raw interior(2) slots(2) by simp
  show ?thesis using proof_node_reading_complete[OF source interior(1) slots(1) at presented] by blast
qed

lemma native_proof_node_value_formed:
  assumes raw: "native_proof_node_at E (fst n) (snd n) N D I K"
    and presented: "proof_node_value_presents N D t"
  shows "term_formed (definition_site_value n)" "term_formed t"
proof -
  obtain e where source: "environment_value_presents E e"
    using environment_value_presents_total[OF native_proof_node_properties(1)[OF raw]] by blast
  obtain Is where interior: "distinct Is" "set Is=I"
    using finite_distinct_list[OF native_proof_node_properties(6)[OF raw]] by blast
  obtain Ks where slots: "distinct Ks" "set Ks=K"
    using finite_distinct_list[OF native_proof_node_properties(7)[OF raw]] by blast
  have at: "native_proof_node_at E (fst n) (snd n) N D (set Is) (set Ks)"
    using raw interior(2) slots(2) by simp
  have read: "(94,term_quotation_argument e (use_data_term (fst n)) (Payload_Term (snd n)) t
      (data_list_term (map Payload_Term Is)) (data_list_term (map Payload_Term Ks)))
    \<in>positive_meaning proof_node_reading_system"
    by (rule proof_node_reading_complete[OF source interior(1) slots(1) at presented])
  show "term_formed (definition_site_value n)" "term_formed t"
    using schema_call_formed_target[OF positive_meaning_formed[OF read]] by auto
qed

lemma environment_position_value_formed:
  assumes formed: "environment_formed E" and position: "n\<in>environment_positions E"
  shows "term_formed (definition_site_value n)"
proof -
  obtain R where source: "artifact_at E (fst n) R" and root: "snd n\<in>rra_carrier (object_structure R)"
    using position by (cases n) auto
  have exact: "exact_formed R" using formed source by (auto simp: environment_formed_def)
  show ?thesis using exact root by (auto simp: exact_formed_def)
qed

lemma native_discharge_values_formed:
  assumes raw: "native_proof_node_at E u r N D I K" and rows: "set ds\<subseteq>D"
  shows "\<forall>(s,n)\<in>set ds. term_formed (definition_site_value s) \<and> term_formed (definition_site_value n)"
  using native_proof_node_properties(9)[OF raw] rows
    environment_position_value_formed[OF native_proof_node_properties(1)[OF raw]] by blast

lemma native_value_rows_entry:
  assumes rows: "native_value_rows E bs" and row: "(n,t)\<in>set bs"
  obtains N D I K where "proof_node_value_presents N D t" "native_proof_node_at E (fst n) (snd n) N D I K"
  using bspec[OF rows row]
  by (simp only: case_prod_conv; elim exE conjE) (rule that; assumption)

lemma native_value_rows_formed:
  assumes rows: "native_value_rows E bs"
  shows "formed_key_rows (map (\<lambda>(n,t). (definition_site_value n,t)) bs)" "term_formed (proof_bound_term bs)"
proof -
  have each: "term_formed (definition_site_value n) \<and> term_formed t" if member: "(n,t)\<in>set bs" for n t
  proof -
    obtain N D I K where presented: "proof_node_value_presents N D t"
      and raw: "native_proof_node_at E (fst n) (snd n) N D I K"
      by (rule native_value_rows_entry[OF rows member]) (rule that; assumption)
    show ?thesis using native_proof_node_value_formed[OF raw presented] by blast
  qed
  have encoded: "formed_key_rows (map (\<lambda>(n,t). (definition_site_value n,t)) bs)"
  proof (intro ballI)
    fix z assume member: "z\<in>set (map (\<lambda>(n,t). (definition_site_value n,t)) bs)"
    obtain n t where row: "(n,t)\<in>set bs" and shape: "z=(definition_site_value n,t)"
      using member by auto
    show "case z of (k,v) \<Rightarrow> term_formed k \<and> self_contained_term k \<and> term_formed v"
      using each[OF row] by (simp add: shape)
  qed
  show "formed_key_rows (map (\<lambda>(n,t). (definition_site_value n,t)) bs)" by (rule encoded)
  show "term_formed (proof_bound_term bs)"
    using pair_list_term_formed[OF encoded] by (simp only: id_apply)
qed

lemma proof_bound_key_absence:
  assumes parent: "term_formed (definition_site_value n)" and rows: "native_value_rows E bs"
  shows "(20,Pair_Term (definition_site_value n) (proof_bound_term bs))\<in>positive_meaning key_absence_system
    \<longleftrightarrow> n\<notin>set (map fst bs)"
proof -
  let ?rows="map (\<lambda>(n,t). (definition_site_value n,t)) bs"
  have formed: "formed_key_rows ?rows" by (rule native_value_rows_formed(1)[OF rows])
  have mapped: "map fst ?rows=map definition_site_value (map fst bs)"
    by (simp add: comp_def case_prod_unfold)
  have absent: "definition_site_value n\<notin>set (map fst ?rows) \<longleftrightarrow> n\<notin>set (map fst bs)"
    by (simp only: mapped set_map image_iff definition_site_value_eq; blast)
  have exact: "(20,Pair_Term (definition_site_value n) (proof_bound_term bs))\<in>positive_meaning key_absence_system \<longleftrightarrow>
    term_formed (definition_site_value n) \<and> self_contained_term (definition_site_value n) \<and>
    formed_key_rows ?rows \<and> definition_site_value n\<notin>set (map fst ?rows)"
    by (simp only: key_absence_exact factor_term.inject pair_list_term_injective id_apply; blast)
  show ?thesis by (simp only: exact absent) (use parent formed in simp)
qed

lemma native_value_rows_key_shape:
  assumes rows: "native_value_rows E bs" and keys: "distinct (map fst bs)"
  shows "(\<exists>t. key_values n bs=[t] \<and>
      (t=Payload_Term [] \<or> (\<exists>c v d. t=data_list_term [c,v,d]))) \<longleftrightarrow> n\<in>set (map fst bs)"
proof
  assume "\<exists>t. key_values n bs=[t] \<and> (t=Payload_Term [] \<or> (\<exists>c v d. t=data_list_term [c,v,d]))"
  then obtain t where fibre: "key_values n bs=[t]" by blast
  have member: "t\<in>set (key_values n bs)" by (simp add: fibre)
  have row: "(n,t)\<in>set bs" using member by (simp only: key_values_set mem_Collect_eq)
  show "n\<in>set (map fst bs)" by (simp only: set_map; rule image_eqI[OF _ row]) simp
next
  assume "n\<in>set (map fst bs)"
  then obtain t where row: "(n,t)\<in>set bs" by auto
  obtain N D I K where presented: "proof_node_value_presents N D t"
    by (rule native_value_rows_entry[OF rows row]) (rule that; assumption)
  have shape: "t=Payload_Term [] \<or> (\<exists>c v d. t=data_list_term [c,v,d])"
    using presented by (cases N) auto
  show "\<exists>t. key_values n bs=[t] \<and> (t=Payload_Term [] \<or> (\<exists>c v d. t=data_list_term [c,v,d]))"
    using key_values_unique_key[OF keys row] shape by blast
qed

lemma native_value_rows_assertion:
  assumes rows: "native_value_rows E bs" and keys: "distinct (map fst bs)" and member: "n\<in>set (map fst bs)"
  shows "key_values n bs=[Payload_Term []] \<longleftrightarrow>
    (\<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K)"
proof -
  obtain t where row: "(n,t)\<in>set bs" using member by auto
  obtain N D I K where presented: "proof_node_value_presents N D t" and raw: "native_proof_node_at E (fst n) (snd n) N D I K"
    by (rule native_value_rows_entry[OF rows row]) (rule that; assumption)
  have fibre: "key_values n bs=[t]" by (rule key_values_unique_key[OF keys row])
  have kind: "(t=Payload_Term []) \<longleftrightarrow> N=Schema_Assertion"
    using presented by (cases N) auto
  have actual: "N=Schema_Assertion \<longleftrightarrow> (\<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K)"
    using raw native_proof_node_assertion[of E "fst n" "snd n" D I K]
      native_proof_node_unique[OF raw] by blast
  show ?thesis by (simp only: fibre list.inject kind actual; simp)
qed

lemma proof_link_rows_on_sites:
  assumes rows: "native_value_rows E bs" and keys: "distinct (map fst bs)"
    and sites: "\<forall>(s,n)\<in>set ds. term_formed (definition_site_value s) \<and> term_formed (definition_site_value n)"
  shows "proof_link_rows (proof_bound_term bs) (definition_site_value p) (encoded_discharge_rows ds) hs \<longleftrightarrow>
    rel_ran (set ds)\<subseteq>set (map fst bs) \<and> hs=native_link_origins E p ds"
  using sites
proof (induction ds arbitrary: hs)
  case Nil
  then show ?case by (simp add: native_link_origins_def rel_ran_def)
next
  case (Cons row ds)
  obtain s n where row: "row=(s,n)" by (cases row)
  have socket: "term_formed (definition_site_value s)" using Cons.prems by (simp add: row)
  have tail_sites: "\<forall>(s,n)\<in>set ds. term_formed (definition_site_value s) \<and> term_formed (definition_site_value n)"
    using Cons.prems by (simp add: row)
  have shape: "(key_values n bs=[Payload_Term []] \<or> (\<exists>c v d. key_values n bs=[data_list_term [c,v,d]]))
      \<longleftrightarrow> n\<in>set (map fst bs)"
    using native_value_rows_key_shape[OF rows keys, of n] by blast
  have assertion: "n\<in>set (map fst bs) \<Longrightarrow>
    (key_values n bs=[Payload_Term []]) \<longleftrightarrow>
      (\<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K)"
    by (rule native_value_rows_assertion[OF rows keys])
  have disjoint: "key_values n bs=[Payload_Term []] \<Longrightarrow>
    key_values n bs\<noteq>[data_list_term [c,v,d]]" for c v d by auto
  let ?rs="map (\<lambda>(n,t). (definition_site_value n,id t)) bs"
  let ?A="\<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K"
  let ?origin="(definition_site_value n,Pair_Term (definition_site_value p) (definition_site_value s))"
  have formed: "formed_key_rows ?rs"
    using native_value_rows_formed(1)[OF rows] by (simp only: id_apply)
  have socket_data: "self_contained_term (definition_site_value s)" by simp
  have fibre: "key_values (definition_site_value n) ?rs=key_values n bs"
    using key_values_map[OF definition_site_value_injective, where g=id and k=n and xs=bs]
    by (simp only: id_def map_ident)
  have step: "proof_link_rows (proof_bound_term bs) (definition_site_value p)
      (encoded_discharge_rows (row#ds)) hs \<longleftrightarrow>
    (\<exists>us. proof_link_rows (proof_bound_term bs) (definition_site_value p) (encoded_discharge_rows ds) us \<and>
      ((key_values n bs=[Payload_Term []] \<and> hs=?origin#us) \<or>
        (\<exists>c v d. key_values n bs=[data_list_term [c,v,d]] \<and> hs=us)))"
  proof
    assume checked: "proof_link_rows (proof_bound_term bs) (definition_site_value p)
      (encoded_discharge_rows (row#ds)) hs"
    have expanded: "proof_link_rows (proof_bound_term bs) (definition_site_value p)
      ((definition_site_value s,definition_site_value n)#encoded_discharge_rows ds) hs"
      using checked by (simp only: row list.map case_prod_conv)
    obtain rs us where decoding: "proof_bound_term bs=pair_list_term rs"
      and tail: "proof_link_rows (proof_bound_term bs) (definition_site_value p) (encoded_discharge_rows ds) us"
      and alternatives: "(key_values (definition_site_value n) rs=[Payload_Term []] \<and> hs=?origin#us) \<or>
        (\<exists>c v d. key_values (definition_site_value n) rs=[data_list_term [c,v,d]] \<and> hs=us)"
      using iffD1[OF proof_link_rows.simps(2) expanded] by blast
    have same: "rs=?rs" using decoding by (simp only: pair_list_term_injective; blast)
    have decoded: "(key_values n bs=[Payload_Term []] \<and> hs=?origin#us) \<or>
      (\<exists>c v d. key_values n bs=[data_list_term [c,v,d]] \<and> hs=us)"
      using alternatives by (simp only: same fibre)
    show "\<exists>us. proof_link_rows (proof_bound_term bs) (definition_site_value p) (encoded_discharge_rows ds) us \<and>
      ((key_values n bs=[Payload_Term []] \<and> hs=?origin#us) \<or>
        (\<exists>c v d. key_values n bs=[data_list_term [c,v,d]] \<and> hs=us))"
      using tail decoded by blast
  next
    assume "\<exists>us. proof_link_rows (proof_bound_term bs) (definition_site_value p) (encoded_discharge_rows ds) us \<and>
      ((key_values n bs=[Payload_Term []] \<and> hs=?origin#us) \<or>
        (\<exists>c v d. key_values n bs=[data_list_term [c,v,d]] \<and> hs=us))"
    then obtain us where tail: "proof_link_rows (proof_bound_term bs) (definition_site_value p) (encoded_discharge_rows ds) us"
      and alternatives: "(key_values n bs=[Payload_Term []] \<and> hs=?origin#us) \<or>
        (\<exists>c v d. key_values n bs=[data_list_term [c,v,d]] \<and> hs=us)" by blast
    have encoded_alternatives: "(key_values (definition_site_value n) ?rs=[Payload_Term []] \<and> hs=?origin#us) \<or>
      (\<exists>c v d. key_values (definition_site_value n) ?rs=[data_list_term [c,v,d]] \<and> hs=us)"
      using alternatives by (simp only: fibre)
    have expanded: "proof_link_rows (proof_bound_term bs) (definition_site_value p)
      ((definition_site_value s,definition_site_value n)#encoded_discharge_rows ds) hs"
      by (rule iffD2[OF proof_link_rows.simps(2)],
          rule exI[of _ "?rs"], rule exI[of _ us])
        (use formed socket socket_data tail encoded_alternatives in blast)
    show "proof_link_rows (proof_bound_term bs) (definition_site_value p) (encoded_discharge_rows (row#ds)) hs"
      using expanded by (simp only: row list.map case_prod_conv)
  qed
  have range: "rel_ran (set (row#ds))=insert n (rel_ran (set ds))"
    by (simp only: row list.set rel_ran_image image_insert snd_conv)
  have origins: "native_link_origins E p (row#ds)=
    (if ?A then ?origin#native_link_origins E p ds else native_link_origins E p ds)"
    by (simp add: row native_link_origins_def)
  show ?case
  proof (cases "n\<in>set (map fst bs)")
    case False
    have no_assertion: "key_values n bs\<noteq>[Payload_Term []]" and no_inference:
      "\<forall>c v d. key_values n bs\<noteq>[data_list_term [c,v,d]]"
      using shape False by blast+
    show ?thesis
      by (simp only: step Cons.IH[OF tail_sites] range insert_subset;
          use False no_assertion no_inference in blast)
  next
    case True
    have member: "n\<in>set (map fst bs)" by (rule True)
    show ?thesis
    proof (cases "?A")
      case True
      have empty: "key_values n bs=[Payload_Term []]"
        using assertion[OF member] True by blast
      have no_inference: "\<forall>c v d. key_values n bs\<noteq>[data_list_term [c,v,d]]"
        using disjoint[OF empty] by blast
      show ?thesis
        by (simp only: step Cons.IH[OF tail_sites] range insert_subset origins True if_True;
            use member empty no_inference in blast)
    next
      case False
      have nonempty: "key_values n bs\<noteq>[Payload_Term []]"
        using assertion[OF member] False by blast
      have inference: "\<exists>c v d. key_values n bs=[data_list_term [c,v,d]]"
        using shape member nonempty by blast
      show ?thesis
        by (simp only: step Cons.IH[OF tail_sites] range insert_subset origins False if_False;
            use member nonempty inference in blast)
    qed
  qed
qed

lemma native_link_origins_distinct:
  assumes "distinct ds"
  shows "distinct (native_link_origins E p ds)"
proof -
  have injective: "inj (\<lambda>(s,n). origin_entry (n,(p,s)))"
    by (rule injI) (auto simp: definition_site_value_eq)
  show ?thesis using assms injective
    by (auto simp: native_link_origins_def distinct_map inj_on_def inj_def)
qed

lemma native_link_origins_parent:
  assumes "q\<in>set (native_link_origins E p ds)"
  shows "\<exists>n s. q=origin_entry (n,(p,s))"
  using assms by (auto simp: native_link_origins_def)

fun proof_bound_values ::
  "local_address option artifact_environment \<Rightarrow>
    (local_address option definition_site\<times>factor_term) list \<Rightarrow>
    (factor_term\<times>factor_term) list \<Rightarrow> bool" where
  "proof_bound_values E [] hs \<longleftrightarrow> hs=[]"
| "proof_bound_values E ((n,t)#bs) hs \<longleftrightarrow> n\<notin>set (map fst bs) \<and>
    (\<exists>N D I K ds us. proof_node_value_presents N D t \<and>
      native_proof_node_at E (fst n) (snd n) N D I K \<and> proof_value_links t ds \<and>
      rel_ran D\<subseteq>set (map fst bs) \<and> proof_bound_values E bs us \<and>
      hs=native_link_origins E n ds @ us)"

lemma proof_bound_values_cons:
  assumes fresh: "n\<notin>set (map fst bs)" and presented: "proof_node_value_presents N D t"
    and raw: "native_proof_node_at E (fst n) (snd n) N D I K" and links: "proof_value_links t ds"
    and children: "rel_ran D\<subseteq>set (map fst bs)" and tail: "proof_bound_values E bs us"
  shows "proof_bound_values E ((n,t)#bs) (native_link_origins E n ds @ us)"
  using assms by (simp only: proof_bound_values.simps; blast)

lemma proof_bound_values_reads:
  assumes bound: "proof_bound_values E bs hs"
  shows "native_value_rows E bs"
  using bound
proof (induction bs arbitrary: hs)
  case Nil
  then show ?case by simp
next
  case (Cons row bs)
  obtain n t where row: "row=(n,t)" by (cases row)
  obtain N D I K us where parts: "proof_node_value_presents N D t"
    "native_proof_node_at E (fst n) (snd n) N D I K" "proof_bound_values E bs us"
    using Cons.prems by (simp only: row proof_bound_values.simps; blast)
  have first: "\<exists>N D I K. proof_node_value_presents N D t \<and> native_proof_node_at E (fst n) (snd n) N D I K"
    using parts(1,2) by blast
  have tail: "native_value_rows E bs" by (rule Cons.IH[OF parts(3)])
  show ?case using first tail by (simp only: row list.set Set.ball_simps(7) case_prod_conv; blast)
qed

lemma proof_bound_values_order:
  assumes bound: "proof_bound_values E bs hs"
  shows "native_node_bound E (map fst bs)"
  using bound
proof (induction bs arbitrary: hs)
  case Nil
  then show ?case by simp
next
  case (Cons row bs)
  obtain n t where row: "row=(n,t)" by (cases row)
  obtain N D I K us where fresh: "n\<notin>set (map fst bs)"
    and raw: "native_proof_node_at E (fst n) (snd n) N D I K"
    and children: "rel_ran D\<subseteq>set (map fst bs)" and rest: "proof_bound_values E bs us"
    using Cons.prems by (simp only: row proof_bound_values.simps; blast)
  have tail: "native_node_bound E (map fst bs)" by (rule Cons.IH[OF rest])
  show ?case using fresh raw children tail by (simp only: row list.map fst_conv native_node_bound.simps; blast)
qed

lemma proof_bound_values_keys:
  assumes bound: "proof_bound_values E bs hs"
  shows "distinct (map fst bs)"
  by (rule children_follow_distinct[OF native_node_bound_order[OF proof_bound_values_order[OF bound]]])

lemma proof_bound_values_formed:
  assumes bound: "proof_bound_values E bs hs"
  shows "term_formed (proof_bound_term bs)" "data_elements (map (\<lambda>(n,q). Pair_Term n q) hs)"
proof -
  show "term_formed (proof_bound_term bs)"
    by (rule native_value_rows_formed(2)[OF proof_bound_values_reads[OF bound]])
  show "data_elements (map (\<lambda>(n,q). Pair_Term n q) hs)"
    using bound
  proof (induction bs arbitrary: hs)
    case Nil
    then show ?case by simp
  next
    case (Cons row bs)
    obtain n t where row: "row=(n,t)" by (cases row)
    obtain N D I K ds us where parts: "proof_node_value_presents N D t"
      "native_proof_node_at E (fst n) (snd n) N D I K" "proof_value_links t ds"
      "rel_ran D\<subseteq>set (map fst bs)" "proof_bound_values E bs us" "hs=native_link_origins E n ds @ us"
      using Cons.prems by (simp only: row proof_bound_values.simps) blast
    obtain es where es: "proof_value_links t es" "distinct es" "set es=D"
      using proof_node_value_links[OF parts(1)] by blast
    have same: "ds=es" by (rule proof_value_links_unique[OF parts(3) es(1)])
    have sites: "\<forall>(s,m)\<in>set ds. term_formed (definition_site_value s) \<and> term_formed (definition_site_value m)"
      by (rule native_discharge_values_formed[OF parts(2)]) (simp add: same es(3))
    have parent: "term_formed (definition_site_value n)" by (rule native_proof_node_value_formed(1)[OF parts(2,1)])
    show ?case using Cons.IH[OF parts(5)] sites parent
      by (auto simp: parts(6) native_link_origins_def)
  qed
qed

lemma native_assertion_origins_insert:
  fixes E :: "'u artifact_environment"
  assumes raw: "native_proof_node_at E (fst p) (snd p) N D I K"
  shows "native_assertion_origins E (insert p A) =
    {(n,(q,s)). q=p \<and> (s,n)\<in>D \<and> (\<exists>J L. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} J L)}
      \<union> native_assertion_origins E A"
proof (rule set_eqI)
  fix row :: "'u definition_site \<times> ('u definition_site \<times> 'u definition_site)"
  obtain n q s where row: "row=(n,(q,s))" by (cases row) auto
  show "row\<in>native_assertion_origins E (insert p A) \<longleftrightarrow>
    row\<in>{(n,(q,s)). q=p \<and> (s,n)\<in>D \<and>
      (\<exists>J L. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} J L)} \<union> native_assertion_origins E A"
  proof (cases "q=p")
    case True
    then show ?thesis by (auto simp: row native_assertion_origins_at_node[OF raw])
  next
    case False
    then show ?thesis by (auto simp: row native_assertion_origins_def)
  qed
qed

lemma native_link_origins_set:
  "set (native_link_origins E p ds) =
    image origin_entry {(n,(q,s)). q=p \<and> (s,n)\<in>set ds \<and>
      (\<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K)}"
proof -
  let ?rows="{z\<in>set ds. case z of (s,n) \<Rightarrow>
    \<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K}"
  have raw_image: "image (\<lambda>(s,n). (n,(p,s))) ?rows =
    {(n,(q,s)). q=p \<and> (s,n)\<in>set ds \<and>
      (\<exists>I K. native_proof_node_at E (fst n) (snd n) Schema_Assertion {} I K)}"
    by (force simp: image_iff split: prod.splits)
  show ?thesis using arg_cong[OF raw_image, of "image origin_entry"]
    by (simp add: native_link_origins_def image_image comp_def case_prod_unfold)
qed

lemma proof_bound_values_origins:
  assumes bound: "proof_bound_values E bs hs"
  shows "set hs=image origin_entry (native_assertion_origins E (set (map fst bs)))"
  using bound
proof (induction bs arbitrary: hs)
  case Nil
  then show ?case by (simp add: native_assertion_origins_def)
next
  case (Cons row bs)
  obtain n t where row: "row=(n,t)" by (cases row)
  obtain N D I K ds us where parts: "proof_node_value_presents N D t"
    "native_proof_node_at E (fst n) (snd n) N D I K" "proof_value_links t ds"
    "proof_bound_values E bs us" "hs=native_link_origins E n ds @ us"
    using Cons.prems by (simp only: row proof_bound_values.simps) blast
  obtain es where es: "proof_value_links t es" "set es=D" using proof_node_value_links[OF parts(1)] by blast
  have same: "set ds=D" using proof_value_links_unique[OF parts(3) es(1)] es(2) by simp
  show ?case by (simp only: row list.map fst_conv list.set set_append parts(5)
      native_assertion_origins_insert[OF parts(2)] image_Un native_link_origins_set
      same Cons.IH[OF parts(4)] Un_assoc)
qed

lemma proof_bound_values_distinct_origins:
  assumes bound: "proof_bound_values E bs hs"
  shows "distinct hs"
  using bound
proof (induction bs arbitrary: hs)
  case Nil
  then show ?case by simp
next
  case (Cons row bs)
  obtain n t where row: "row=(n,t)" by (cases row)
  obtain N D I K ds us where fresh: "n\<notin>set (map fst bs)"
    and parts: "proof_node_value_presents N D t" "proof_value_links t ds"
      "proof_bound_values E bs us" "hs=native_link_origins E n ds @ us"
    using Cons.prems by (simp only: row proof_bound_values.simps) blast
  obtain es where es: "proof_value_links t es" "distinct es" using proof_node_value_links[OF parts(1)] by blast
  have distinct: "distinct ds" using proof_value_links_unique[OF parts(2) es(1)] es(2) by simp
  have first: "distinct (native_link_origins E n ds)" by (rule native_link_origins_distinct[OF distinct])
  have tail: "distinct us" by (rule Cons.IH[OF parts(3)])
  have tail_parent: "\<exists>m p s. p\<in>set (map fst bs) \<and> q=origin_entry (m,(p,s))" if member: "q\<in>set us" for q
  proof -
    have image_member: "q\<in>image origin_entry (native_assertion_origins E (set (map fst bs)))"
      using member proof_bound_values_origins[OF parts(3)] by simp
    obtain z where actual: "z\<in>native_assertion_origins E (set (map fst bs))" and row_value: "q=origin_entry z"
      using image_member by blast
    obtain m p s where shape: "z=(m,(p,s))" by (cases z) auto
    have parent: "p\<in>set (map fst bs)"
      using actual by (simp only: shape native_assertion_origins_def mem_Collect_eq case_prod_conv; blast)
    show ?thesis using parent row_value shape by blast
  qed
  have separate: "set (native_link_origins E n ds)\<inter>set us={}"
  proof (rule equals0I)
    fix q
    assume both: "q\<in>set (native_link_origins E n ds)\<inter>set us"
    have head_member: "q\<in>set (native_link_origins E n ds)" and tail_member: "q\<in>set us"
      using both by blast+
    obtain m s where head_row: "q=origin_entry (m,(n,s))"
      using native_link_origins_parent[OF head_member] by blast
    obtain l p r where parent: "p\<in>set (map fst bs)" and tail_row: "q=origin_entry (l,(p,r))"
      using tail_parent[OF tail_member] by blast
    have same: "(m,(n,s))=(l,(p,r))"
      by (rule injD[OF origin_entry_injective]) (use head_row tail_row in blast)
    have parents: "n=p" using same by (simp only: prod.inject; blast)
    show False using fresh parent parents by blast
  qed
  show ?case using first tail separate by (simp add: parts(4))
qed

lemma native_node_bound_values:
  assumes bound: "native_node_bound E ns"
  shows "\<exists>bs hs. map fst bs=ns \<and> proof_bound_values E bs hs"
  using bound
proof (induction ns)
  case Nil
  then show ?case by (rule_tac x="[]" in exI, rule_tac x="[]" in exI) simp
next
  case (Cons n ns)
  have fresh: "n\<notin>set ns" and tail: "native_node_bound E ns" using Cons.prems by auto
  obtain N D I K where raw: "native_proof_node_at E (fst n) (snd n) N D I K"
    and children: "rel_ran D\<subseteq>set ns" using Cons.prems by auto
  obtain bs us where rest: "map fst bs=ns" "proof_bound_values E bs us" using Cons.IH[OF tail] by blast
  obtain t where presented: "proof_node_value_presents N D t" using proof_node_value_total[OF raw] by blast
  obtain ds where links: "proof_value_links t ds" using proof_node_value_links[OF presented] by blast
  have extended: "proof_bound_values E ((n,t)#bs) (native_link_origins E n ds @ us)"
    by (rule proof_bound_values_cons[OF _ presented raw links _ rest(2)])
      (use fresh children rest(1) in simp_all)
  show ?case by (rule exI[of _ "(n,t)#bs"], rule exI[of _ "native_link_origins E n ds @ us"])
    (use rest(1) extended in simp)
qed

lemma single_valued_origin_image:
  "single_valued (image origin_entry H) \<longleftrightarrow> single_valued H"
proof -
  let ?f="definition_site_value"
  let ?g="\<lambda>(p,s). Pair_Term (definition_site_value p) (definition_site_value s)"
  have encoded: "origin_entry=(\<lambda>(n,q). (?f n,?g q))"
    by (rule ext) (simp add: case_prod_unfold)
  have val_inj: "inj ?g"
    by (rule injI; rename_tac x y; case_tac x; case_tac y)
      (simp only: case_prod_conv factor_term.inject definition_site_value_eq prod.inject)
  show ?thesis
  proof
    assume encoded_sv: "single_valued (image origin_entry H)"
    show "single_valued H"
      unfolding single_valued_def
    proof (intro allI impI)
      fix n x y assume first: "(n,x)\<in>H" and second: "(n,y)\<in>H"
      have left: "(?f n,?g x)\<in>image origin_entry H"
        using imageI[OF first, of origin_entry]
          by (simp only: case_prod_unfold fst_conv snd_conv)
      have right: "(?f n,?g y)\<in>image origin_entry H"
        using imageI[OF second, of origin_entry]
          by (simp only: case_prod_unfold fst_conv snd_conv)
      have same: "?g x=?g y" by (rule single_valued_outputs[OF encoded_sv left right])
      show "x=y" by (rule injD[OF val_inj same])
    qed
  next
    assume raw_sv: "single_valued H"
    have keys: "inj_on ?f (rel_dom H)" by (rule inj_on_subset[OF definition_site_value_injective]) simp
    have mapped: "single_valued (image (\<lambda>(n,q). (?f n,?g q)) H)"
      by (rule single_valued_pair_image[OF raw_sv keys])
    show "single_valued (image origin_entry H)" using mapped by (simp only: encoded)
  qed
qed

lemma proof_bound_assertion_keys:
  assumes bound: "proof_bound_values E bs hs"
  shows "(21,pair_list_term hs)\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    single_valued (native_assertion_origins E (set (map fst bs)))"
proof -
  have formed: "formed_key_rows hs" using proof_bound_values_formed(2)[OF bound] by auto
  have distinct: "distinct hs" by (rule proof_bound_values_distinct_origins[OF bound])
  show ?thesis
    by (simp only: keyed_list_exact pair_list_term_injective; simp add: formed distinct_keys_iff distinct
        proof_bound_values_origins[OF bound] single_valued_origin_image)
qed

theorem native_graph_value_bound:
  "(\<exists>G. native_schema_graph_at E root G) \<longleftrightarrow>
    (\<exists>bs hs. proof_bound_values E bs hs \<and> root\<in>set (map fst bs) \<and>
      (21,pair_list_term hs)\<in>positive_meaning keyed_list_system)"
proof
  assume "\<exists>G. native_schema_graph_at E root G"
  then obtain ns where bound: "native_node_bound E ns" and root: "root\<in>set ns"
    and origins: "single_valued (native_assertion_origins E (set ns))"
    by (simp only: native_graph_finite_bound) blast
  obtain bs hs where collected: "map fst bs=ns" "proof_bound_values E bs hs"
    using native_node_bound_values[OF bound] by blast
  have keys: "(21,pair_list_term hs)\<in>positive_meaning keyed_list_system"
    using origins by (simp only: proof_bound_assertion_keys[OF collected(2)] collected(1))
  show "\<exists>bs hs. proof_bound_values E bs hs \<and> root\<in>set (map fst bs) \<and>
    (21,pair_list_term hs)\<in>positive_meaning keyed_list_system"
    using collected root keys by blast
next
  assume "\<exists>bs hs. proof_bound_values E bs hs \<and> root\<in>set (map fst bs) \<and>
    (21,pair_list_term hs)\<in>positive_meaning keyed_list_system"
  then obtain bs hs where bound: "proof_bound_values E bs hs" and root: "root\<in>set (map fst bs)"
    and keys: "(21,pair_list_term hs)\<in>positive_meaning keyed_list_system" by blast
  have order: "native_node_bound E (map fst bs)" by (rule proof_bound_values_order[OF bound])
  have origins: "single_valued (native_assertion_origins E (set (map fst bs)))"
    using keys by (simp only: proof_bound_assertion_keys[OF bound])
  show "\<exists>G. native_schema_graph_at E root G"
    using order root origins by (simp only: native_graph_finite_bound) blast
qed

text \<open>
  Bound rows are keyed by actual node sites and carry the existing complete
  node values. The list is a temporary witness, not an added native proof
  field. Its complete assertion-origin list follows the chosen node and
  premise enumerations, with every origin occurring once. Requiring unique
  keys in that list is exactly functional assertion use in the bound.
  Values containing literal targets are retained without data-only comparison.
  Existence of a checked value bound is exactly existence of the existing
  native graph at the supplied root.
\<close>

end
