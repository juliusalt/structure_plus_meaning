theory Factor_Environment_Additions
  imports Factor_Package_Additions Factor_Environment_Inclusion Factor_Reader_Payloads
begin

section \<open>The rows of an environment, presented as data\<close>

text \<open>
  The two tables of an environment are presented by the environment value's own row presentations
  (@{const environment_artifact_entry_presents}, @{const binding_data}), each collection admitting every
  enumeration (@{const data_collection_presents}). A pair of tables is presented so whether or not it is a
  formed environment: the environment value is its presentation at a formed environment.
\<close>

definition environment_rows_presents ::
  "(local_address option\<times>exact_artifact) set \<times> ((local_address option\<times>local_address)\<times>local_address option) set \<Rightarrow>
    factor_term \<Rightarrow> bool" where
  "environment_rows_presents z t \<longleftrightarrow>
    (\<exists>a b. data_collection_presents environment_artifact_entry_presents (fst z) a \<and>
      data_collection_presents (\<lambda>z v. v=binding_data z) (snd z) b \<and> t=Pair_Term a b)"

lemma environment_value_rows:
  "environment_value_presents E t \<longleftrightarrow> environment_formed E \<and>
    environment_rows_presents (environment_artifacts E,environment_bindings E) t"
  by (auto simp: environment_value_presents_def environment_rows_presents_def)

lemma environment_rows_unique:
  assumes first: "environment_rows_presents x t" and second: "environment_rows_presents y t"
  shows "x=y"
proof -
  obtain a b where left: "data_collection_presents environment_artifact_entry_presents (fst x) a"
    "data_collection_presents (\<lambda>z v. v=binding_data z) (snd x) b" "t=Pair_Term a b"
    using first unfolding environment_rows_presents_def by blast
  obtain c d where right: "data_collection_presents environment_artifact_entry_presents (fst y) c"
    "data_collection_presents (\<lambda>z v. v=binding_data z) (snd y) d" "t=Pair_Term c d"
    using second unfolding environment_rows_presents_def by blast
  have same: "c=a" "d=b" using left(3) right(3) by simp_all
  have artifacts: "fst x=fst y"
    by (rule data_collection_presents_unique[OF left(1) right(1)[unfolded same]])
       (rule environment_artifact_entry_unique; assumption)
  have bindings: "snd x=snd y"
    by (rule data_collection_presents_unique[OF left(2) right(2)[unfolded same]])
       (auto dest: injD[OF binding_data_injective])
  show ?thesis using artifacts bindings by (rule prod_eqI)
qed

lemma entry_collection_rows:
  assumes rows: "data_collection_presents environment_artifact_entry_presents A a"
  shows "finite A" and "\<And>u R. (u,R)\<in>A \<Longrightarrow> exact_formed R"
proof -
  obtain xs ts where enumeration: "set xs=A" "list_all2 environment_artifact_entry_presents xs ts"
    using rows unfolding data_collection_presents_def by blast
  show "finite A" using enumeration(1) by blast
  fix u R assume member: "(u,R)\<in>A"
  obtain x where "environment_artifact_entry_presents (u,R) x"
    using list_all2_members[OF enumeration(2)] member enumeration(1) by blast
  then obtain v where "artifact_value_presents R v" unfolding environment_artifact_entry_presents_def by auto
  then show "exact_formed R" using artifact_value_presents_formed by blast
qed

lemma environment_rows_total:
  assumes fa: "finite A" and fb: "finite B" and rows: "\<And>u R. (u,R)\<in>A \<Longrightarrow> exact_formed R"
  shows "\<exists>t. environment_rows_presents (A,B) t"
proof -
  have entries: "\<forall>z\<in>A. \<exists>t. environment_artifact_entry_presents z t"
  proof
    fix z assume member: "z\<in>A"
    obtain v where "artifact_value_presents (snd z) v"
      using artifact_value_presents_total rows[of "fst z" "snd z"] member by auto
    then show "\<exists>t. environment_artifact_entry_presents z t" unfolding environment_artifact_entry_presents_def by blast
  qed
  obtain a where a: "data_collection_presents environment_artifact_entry_presents A a"
    using data_collection_presents_total[OF fa entries] by blast
  obtain b where b: "data_collection_presents (\<lambda>z v. v=binding_data z) B b"
    using data_collection_presents_total[OF fb, of "\<lambda>z v. v=binding_data z"] by blast
  show ?thesis using a b unfolding environment_rows_presents_def by auto
qed

section \<open>The additions of an environment to another\<close>

text \<open>
  An environment is extended by artifact rows at uses it does not hold and by bindings sourced at those
  uses: the extension is the merge (@{const merge_environment}) of the environment and the added
  material, so every row and binding of the environment stands unchanged in it
  (@{thm [source] environment_included_merge_left}). The additions are that material as data, with a
  site of the extension: the added rows and bindings in the environment value's row presentations and
  the site as the site value presents it (@{const site_data_term}). No tag and no other row form.
\<close>

definition environment_extension ::
  "'u artifact_environment \<Rightarrow> ('u\<times>exact_artifact) set \<Rightarrow> (('u\<times>local_address)\<times>'u) set \<Rightarrow>
    'u artifact_environment" where
  "environment_extension E A B=merge_environment E \<lparr>environment_artifacts=A,environment_bindings=B\<rparr>"

lemma environment_extension_fields [simp]:
  "environment_artifacts (environment_extension E A B)=environment_artifacts E \<union> A"
  "environment_bindings (environment_extension E A B)=environment_bindings E \<union> B"
  by (simp_all add: environment_extension_def merge_environment_def)

lemma environment_extension_included: "environment_included E (environment_extension E A B)"
  unfolding environment_extension_def by (rule environment_included_merge_left)

definition environment_additions ::
  "'u artifact_environment \<Rightarrow> ('u\<times>exact_artifact) set \<Rightarrow> (('u\<times>local_address)\<times>'u) set \<Rightarrow> bool" where
  "environment_additions E A B \<longleftrightarrow> environment_formed E \<and> finite A \<and> finite B \<and>
    rel_dom A \<inter> environment_uses E={} \<and> (\<forall>z\<in>B. fst (fst z)\<in>rel_dom A)"

definition additions_value_presents ::
  "((local_address option\<times>exact_artifact) set \<times> ((local_address option\<times>local_address)\<times>local_address option) set)
    \<times> (local_address option\<times>local_address) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "additions_value_presents z t \<longleftrightarrow>
    (\<exists>p. environment_rows_presents (fst z) p \<and> t=Pair_Term p (site_data_term (fst (snd z)) (snd (snd z))))"

lemma additions_value_unique:
  assumes first: "additions_value_presents x t" and second: "additions_value_presents y t"
  shows "x=y"
proof -
  obtain p where p: "environment_rows_presents (fst x) p" "t=Pair_Term p (site_data_term (fst (snd x)) (snd (snd x)))"
    using first unfolding additions_value_presents_def by blast
  obtain q where q: "environment_rows_presents (fst y) q" "t=Pair_Term q (site_data_term (fst (snd y)) (snd (snd y)))"
    using second unfolding additions_value_presents_def by blast
  have same: "q=p" and site: "use_data_term (fst (snd x))=use_data_term (fst (snd y))" "snd (snd x)=snd (snd y)"
    using p(2) q(2) by (simp_all add: site_data_term_def)
  have rows: "fst x=fst y" by (rule environment_rows_unique[OF p(1) q(1)[unfolded same]])
  have uses: "fst (snd x)=fst (snd y)" by (rule injD[OF use_data_term_injective site(1)])
  show ?thesis using rows uses site(2) by (simp add: prod_eq_iff)
qed

section \<open>The extension is formed exactly when its added material is\<close>

theorem environment_extension_formed_iff:
  assumes additions: "environment_additions E A B"
  shows "environment_formed (environment_extension E A B) \<longleftrightarrow>
    single_valued A \<and> (\<forall>z\<in>A. exact_formed (snd z)) \<and> single_valued B \<and>
    (\<forall>z\<in>B. (\<exists>R. (fst (fst z),R)\<in>A \<and> snd (fst z)\<in>rra_carrier (object_structure R)) \<and>
      snd z\<in>rel_dom A \<union> environment_uses E)"
proof -
  have ef: "environment_formed E" and fa: "finite A" and fb: "finite B"
    and disjoint: "rel_dom A \<inter> environment_uses E={}" and sources: "\<forall>z\<in>B. fst (fst z)\<in>rel_dom A"
    using additions unfolding environment_additions_def by blast+
  have fresh: "(u,S)\<notin>environment_artifacts E" if "(u,R)\<in>A" for u R S
    using disjoint that by (auto simp: environment_uses_def rel_dom_def)
  have sourced: "\<exists>R. (u,R)\<in>A" if "((u,k),v)\<in>B" for u k v
    using sources that by (force simp: rel_dom_def)
  have old: "(\<exists>R. (u,R)\<in>environment_artifacts E \<and> k\<in>rra_carrier (object_structure R)) \<and>
      v\<in>environment_uses E" if "((u,k),v)\<in>environment_bindings E" for u k v
    using ef that unfolding environment_formed_def binds_slot_def artifact_at_def by blast
  have finE: "finite (environment_artifacts E)" "finite (environment_bindings E)"
    and svE: "single_valued (environment_artifacts E)" "single_valued (environment_bindings E)"
    and valE: "\<And>u R. (u,R)\<in>environment_artifacts E \<Longrightarrow> exact_formed R"
    using ef unfolding environment_formed_def artifact_at_def by blast+
  have artifacts: "single_valued (environment_artifacts E \<union> A) \<longleftrightarrow> single_valued A"
  proof
    assume "single_valued (environment_artifacts E \<union> A)"
    then show "single_valued A" unfolding single_valued_def by blast
  next
    assume sv: "single_valued A"
    show "single_valued (environment_artifacts E \<union> A)" unfolding single_valued_def
    proof (intro allI impI)
      fix x y z assume "(x,y)\<in>environment_artifacts E \<union> A" "(x,z)\<in>environment_artifacts E \<union> A"
      then show "y=z" using sv svE fresh unfolding single_valued_def by blast
    qed
  qed
  have bindings: "single_valued (environment_bindings E \<union> B) \<longleftrightarrow> single_valued B"
  proof
    assume "single_valued (environment_bindings E \<union> B)"
    then show "single_valued B" unfolding single_valued_def by blast
  next
    assume sv: "single_valued B"
    show "single_valued (environment_bindings E \<union> B)" unfolding single_valued_def
    proof (intro allI impI)
      fix x y z assume first: "(x,y)\<in>environment_bindings E \<union> B" and second: "(x,z)\<in>environment_bindings E \<union> B"
      obtain u k where x: "x=(u,k)" by (cases x) auto
      have apart: "\<not> ((x,w)\<in>environment_bindings E \<and> (x,w')\<in>B)" for w w'
      proof
        assume both: "(x,w)\<in>environment_bindings E \<and> (x,w')\<in>B"
        obtain R where "(u,R)\<in>environment_artifacts E" using old[of u k w] both x by blast
        moreover obtain S where "(u,S)\<in>A" using sourced[of u k w'] both x by blast
        ultimately show False using fresh by blast
      qed
      show "y=z" using first second apart sv svE unfolding single_valued_def by blast
    qed
  qed
  have formations: "(\<forall>u R. (u,R)\<in>environment_artifacts E \<union> A \<longrightarrow> exact_formed R) \<longleftrightarrow> (\<forall>z\<in>A. exact_formed (snd z))"
  proof
    assume "\<forall>u R. (u,R)\<in>environment_artifacts E \<union> A \<longrightarrow> exact_formed R"
    then show "\<forall>z\<in>A. exact_formed (snd z)" by force
  next
    assume "\<forall>z\<in>A. exact_formed (snd z)"
    then show "\<forall>u R. (u,R)\<in>environment_artifacts E \<union> A \<longrightarrow> exact_formed R" using valE by force
  qed
  have uses: "rel_dom (environment_artifacts E \<union> A)=rel_dom A \<union> environment_uses E"
    by (auto simp: rel_dom_def environment_uses_def)
  have references: "(\<forall>u k v. ((u,k),v)\<in>environment_bindings E \<union> B \<longrightarrow>
      (\<exists>R. (u,R)\<in>environment_artifacts E \<union> A \<and> k\<in>rra_carrier (object_structure R)) \<and>
      v\<in>rel_dom (environment_artifacts E \<union> A)) \<longleftrightarrow>
    (\<forall>z\<in>B. (\<exists>R. (fst (fst z),R)\<in>A \<and> snd (fst z)\<in>rra_carrier (object_structure R)) \<and>
      snd z\<in>rel_dom A \<union> environment_uses E)" (is "?l \<longleftrightarrow> ?r")
  proof
    assume left: ?l
    show ?r
    proof
      fix z assume member: "z\<in>B"
      obtain u k v where z: "z=((u,k),v)" by (metis prod.collapse)
      obtain R where row: "(u,R)\<in>environment_artifacts E \<union> A" "k\<in>rra_carrier (object_structure R)"
        and target: "v\<in>rel_dom (environment_artifacts E \<union> A)" using left member z by blast
      obtain S where "(u,S)\<in>A" using sourced member z by blast
      then have "(u,R)\<in>A" using row(1) fresh by blast
      then show "(\<exists>R. (fst (fst z),R)\<in>A \<and> snd (fst z)\<in>rra_carrier (object_structure R)) \<and>
        snd z\<in>rel_dom A \<union> environment_uses E" using row(2) target uses z by auto
    qed
  next
    assume right: ?r
    show ?l
    proof (intro allI impI)
      fix u k v assume member: "((u,k),v)\<in>environment_bindings E \<union> B"
      show "(\<exists>R. (u,R)\<in>environment_artifacts E \<union> A \<and> k\<in>rra_carrier (object_structure R)) \<and>
        v\<in>rel_dom (environment_artifacts E \<union> A)"
      proof (cases "((u,k),v)\<in>environment_bindings E")
        case True then show ?thesis using old[of u k v] uses by blast
      next
        case False then have "((u,k),v)\<in>B" using member by blast
        then show ?thesis using right uses by fastforce
      qed
    qed
  qed
  have unfolded: "environment_formed (environment_extension E A B) \<longleftrightarrow>
      finite (environment_artifacts E \<union> A) \<and> single_valued (environment_artifacts E \<union> A) \<and>
      (\<forall>u R. (u,R)\<in>environment_artifacts E \<union> A \<longrightarrow> exact_formed R) \<and>
      finite (environment_bindings E \<union> B) \<and> single_valued (environment_bindings E \<union> B) \<and>
      (\<forall>u k v. ((u,k),v)\<in>environment_bindings E \<union> B \<longrightarrow>
        (\<exists>R. (u,R)\<in>environment_artifacts E \<union> A \<and> k\<in>rra_carrier (object_structure R)) \<and>
        v\<in>rel_dom (environment_artifacts E \<union> A))"
    by (simp only: environment_formed_def artifact_at_def binds_slot_def environment_uses_def
      environment_extension_fields)
  show ?thesis unfolding unfolded artifacts bindings formations references using finE fa fb by simp
qed

section \<open>The class of additions relative to a given environment\<close>

text \<open>
  The subject is an extension of a formed environment E with a site of it: a formed environment including
  E whose bindings not of E are sourced at uses E does not hold. Its additions are its rows and bindings
  that are not E's. The domain's restriction to bindings sourced at added uses is a residual choice (task
  928's verdict, answer 2): an answer adds its own artifacts and their bindings, so the given's readings
  stay exact under it; a binding at an address of a given artifact is not a candidate.
\<close>

definition added_rows ::
  "'u artifact_environment \<Rightarrow> 'u artifact_environment \<Rightarrow>
    ('u\<times>exact_artifact) set \<times> (('u\<times>local_address)\<times>'u) set" where
  "added_rows E F=(environment_artifacts F-environment_artifacts E,environment_bindings F-environment_bindings E)"

definition additions_domain ::
  "local_address option artifact_environment \<Rightarrow>
    local_address option artifact_environment \<times> (local_address option\<times>local_address) \<Rightarrow> bool" where
  "additions_domain E z \<longleftrightarrow> environment_formed E \<and> environment_formed (fst z) \<and> environment_included E (fst z) \<and>
    (\<forall>b\<in>environment_bindings (fst z)-environment_bindings E. fst (fst b)\<notin>environment_uses E) \<and>
    snd z\<in>environment_positions (fst z)"

definition additions_presents ::
  "local_address option artifact_environment \<Rightarrow>
    local_address option artifact_environment \<times> (local_address option\<times>local_address) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "additions_presents E z t \<longleftrightarrow> additions_domain E z \<and> additions_value_presents (added_rows E (fst z),snd z) t"

lemma additions_domain_extension:
  assumes domain: "additions_domain E (F,s)"
  shows "environment_additions E (fst (added_rows E F)) (snd (added_rows E F))"
    and "F=environment_extension E (fst (added_rows E F)) (snd (added_rows E F))"
proof -
  have ef: "environment_formed E" and ff: "environment_formed F" and included: "environment_included E F"
    and outside: "\<forall>b\<in>environment_bindings F-environment_bindings E. fst (fst b)\<notin>environment_uses E"
    using domain unfolding additions_domain_def by auto
  have subsets: "environment_artifacts E\<subseteq>environment_artifacts F" "environment_bindings E\<subseteq>environment_bindings F"
    using included unfolding environment_included_def by auto
  have finite: "finite (environment_artifacts F)" "finite (environment_bindings F)"
    and svF: "single_valued (environment_artifacts F)"
    using ff unfolding environment_formed_def by auto
  have fresh: "rel_dom (environment_artifacts F-environment_artifacts E)\<inter>environment_uses E={}"
  proof -
    have False if new: "(u,R)\<in>environment_artifacts F-environment_artifacts E" and old: "u\<in>environment_uses E" for u R
    proof -
      obtain S where given: "(u,S)\<in>environment_artifacts E" using old by (auto simp: environment_uses_def rel_dom_def)
      then have "(u,S)\<in>environment_artifacts F" "(u,R)\<in>environment_artifacts F" using subsets new by auto
      then have "R=S" using svF unfolding single_valued_def by blast
      then show False using new given by simp
    qed
    then show ?thesis by (auto simp: rel_dom_def)
  qed
  have sourced: "\<forall>b\<in>environment_bindings F-environment_bindings E.
      fst (fst b)\<in>rel_dom (environment_artifacts F-environment_artifacts E)"
  proof
    fix b assume new: "b\<in>environment_bindings F-environment_bindings E"
    obtain u k v where b: "b=((u,k),v)" by (metis prod.collapse)
    obtain R where row: "(u,R)\<in>environment_artifacts F"
      using ff new b unfolding environment_formed_def binds_slot_def artifact_at_def by blast
    have "u\<notin>environment_uses E" using outside[rule_format, OF new] b by simp
    then show "fst (fst b)\<in>rel_dom (environment_artifacts F-environment_artifacts E)"
      using row b by (auto simp: rel_dom_def environment_uses_def)
  qed
  show "environment_additions E (fst (added_rows E F)) (snd (added_rows E F))"
    using ef finite fresh sourced by (simp add: environment_additions_def added_rows_def)
  show "F=environment_extension E (fst (added_rows E F)) (snd (added_rows E F))"
    using subsets by (cases F) (auto simp: environment_extension_def merge_environment_def added_rows_def)
qed

lemma extension_additions_domain:
  assumes additions: "environment_additions E A B" and formed: "environment_formed (environment_extension E A B)"
    and site: "s\<in>environment_positions (environment_extension E A B)"
  shows "added_rows E (environment_extension E A B)=(A,B)"
    and "additions_domain E (environment_extension E A B,s)"
proof -
  have ef: "environment_formed E" and disjoint: "rel_dom A\<inter>environment_uses E={}"
    and sources: "\<forall>z\<in>B. fst (fst z)\<in>rel_dom A"
    using additions unfolding environment_additions_def by blast+
  have apart: "A\<inter>environment_artifacts E={}"
    using disjoint by (auto simp: rel_dom_def environment_uses_def)
  have old: "fst (fst b)\<in>environment_uses E" if member: "b\<in>environment_bindings E" for b
  proof -
    obtain u k v where b: "b=((u,k),v)" by (metis prod.collapse)
    obtain R where "(u,R)\<in>environment_artifacts E"
      using ef member b unfolding environment_formed_def binds_slot_def artifact_at_def by blast
    then show ?thesis using b by (auto simp: environment_uses_def rel_dom_def)
  qed
  have separate: "B\<inter>environment_bindings E={}" using old sources disjoint by blast
  show rows: "added_rows E (environment_extension E A B)=(A,B)" using apart separate by (auto simp: added_rows_def)
  have "environment_bindings (environment_extension E A B)-environment_bindings E=B"
    using rows by (simp add: added_rows_def)
  then show "additions_domain E (environment_extension E A B,s)"
    using ef formed site sources disjoint environment_extension_included[of E A B]
    by (auto simp: additions_domain_def)
qed

theorem additions_presentation_class:
  "presentation_class (additions_presents E) (additions_domain E) (\<lambda>t. \<exists>z. additions_presents E z t)"
proof (rule presentation_class.intro)
  fix z t assume "additions_presents E z t"
  then show "additions_domain E z" by (simp add: additions_presents_def)
next
  fix z t assume "additions_presents E z t" then show "\<exists>z. additions_presents E z t" by blast
next
  fix z assume domain: "additions_domain E z"
  obtain F s where z: "z=(F,s)" by (cases z)
  have ff: "environment_formed F" using domain z by (simp add: additions_domain_def)
  have "\<exists>p. environment_rows_presents (added_rows E F) p"
    using ff unfolding added_rows_def environment_formed_def artifact_at_def
    by (intro environment_rows_total) auto
  then obtain p where "environment_rows_presents (added_rows E F) p" by blast
  then have "additions_value_presents (added_rows E F,s) (Pair_Term p (site_data_term (fst s) (snd s)))"
    by (auto simp: additions_value_presents_def)
  then show "\<exists>t. additions_presents E z t" using domain z by (auto simp: additions_presents_def)
next
  fix t assume "\<exists>z. additions_presents E z t" then show "\<exists>z. additions_presents E z t" .
next
  fix z w t assume first: "additions_presents E z t" and second: "additions_presents E w t"
  obtain F s where z: "z=(F,s)" by (cases z)
  obtain G r where w: "w=(G,r)" by (cases w)
  have "(added_rows E F,s)=(added_rows E G,r)"
    by (rule additions_value_unique[where t=t]) (use first second z w in \<open>simp_all add: additions_presents_def\<close>)
  moreover have "F=environment_extension E (fst (added_rows E F)) (snd (added_rows E F))"
    by (rule additions_domain_extension(2)[of E F s]) (use first z in \<open>simp add: additions_presents_def\<close>)
  moreover have "G=environment_extension E (fst (added_rows E G)) (snd (added_rows E G))"
    by (rule additions_domain_extension(2)[of E G r]) (use second w in \<open>simp add: additions_presents_def\<close>)
  ultimately show "z=w" using z w by auto
qed

text \<open>
  The class is exact relative to the given environment: the additions and E determine the extension and
  the site, which is the merge of E with the added material. It is complete over the extensions it
  concerns: every added material whose extension is formed, with a site of it, is presented.
\<close>

lemma additions_presents_extension:
  assumes presented: "additions_presents E (F,s) t" and valued: "additions_value_presents ((A,B),s') t"
  shows "F=environment_extension E A B" and "s=s'" and "environment_additions E A B"
proof -
  have "(added_rows E F,s)=((A,B),s')"
    by (rule additions_value_unique) (use presented valued in \<open>simp_all add: additions_presents_def\<close>)
  then have rows: "added_rows E F=(A,B)" and "s=s'" by simp_all
  then show "s=s'" by simp
  have domain: "additions_domain E (F,s)" using presented by (simp add: additions_presents_def)
  show "F=environment_extension E A B" using additions_domain_extension(2)[OF domain] rows by simp
  show "environment_additions E A B" using additions_domain_extension(1)[OF domain] rows by simp
qed

lemma extension_additions_presents:
  assumes additions: "environment_additions E A B" and formed: "environment_formed (environment_extension E A B)"
    and site: "s\<in>environment_positions (environment_extension E A B)"
    and valued: "additions_value_presents ((A,B),s) t"
  shows "additions_presents E (environment_extension E A B,s) t"
  using extension_additions_domain[OF additions formed site] valued by (simp add: additions_presents_def)

section \<open>G1's reader: the extension's formation\<close>

text \<open>
  The reader's argument is the pair of the given's environment value and the additions. It admits the
  given (26), each added row (the complete list, 23 over 22), checks each added use absent among the
  given's use keys (key absence at 20 against the given's artifact table), the added uses and the added
  binding keys each unique (21), and each added binding supported: its source and slot read over the
  added rows (24), its target an added use (24 over the added rows) or a use of the given's, read by 37 at
  the given's value. No call carries the given's artifact table as the context of an added binding's
  source or slot. The five definitions stand at 950 to 954, above every numbered site of the library, as
  views over the environment lookup (37), a system below the callee boundary's in its lineage.
\<close>

definition added_use_fresh_schema :: "(nat,nat,nat) factor_schema" where
  "added_use_fresh_schema=data_rule (Pattern_Pair data_x (Pattern_Pair data_y data_z)) {(0,20,Pattern_Pair data_y data_x)}"

definition added_binding_added_schema :: "(nat,nat,nat) factor_schema" where
  "added_binding_added_schema=data_rule (Pattern_Pair (Pattern_Pair data_x data_y) data_z) {(0,24,Pattern_Pair data_x data_z)}"

definition added_binding_given_schema :: "(nat,nat,nat) factor_schema" where
  "added_binding_given_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Pair data_z data_w) (Pattern_Variable 4)))
    {(0,24,Pattern_Pair data_x (Pattern_Pair (Pattern_Pair data_z data_w) data_z)),
     (1,37,Pattern_Pair data_y (Pattern_Pair (Pattern_Variable 4) (Pattern_Variable 5)))}"

definition added_binding_clauses :: "(nat \<times> (nat,nat,nat) factor_schema) set" where
  "added_binding_clauses={(0,added_binding_added_schema),(1,added_binding_given_schema)}"

definition extension_formation_schema :: "(nat,nat,nat) factor_schema" where
  "extension_formation_schema=data_rule
    (Pattern_Pair (Pattern_Pair data_x data_y) (Pattern_Pair (Pattern_Pair data_z data_w) (Pattern_Variable 4)))
    {(0,26,Pattern_Pair data_x data_y),(1,23,data_z),(2,21,data_z),(3,951,Pattern_Pair data_x data_z),
     (4,21,data_w),(5,953,Pattern_Pair (Pattern_Pair data_z (Pattern_Pair data_x data_y)) data_w)}"

definition added_use_fresh_system :: "(nat,nat,nat,nat) schema_system" where
  "added_use_fresh_system=add_view_definition artifact_lookup_system 950 data_x {(0,added_use_fresh_schema)}"

definition added_uses_fresh_system :: "(nat,nat,nat,nat) schema_system" where
  "added_uses_fresh_system=add_view_definition added_use_fresh_system 951 data_x (context_list_clauses 950 951)"

definition added_binding_system :: "(nat,nat,nat,nat) schema_system" where
  "added_binding_system=add_view_definition added_uses_fresh_system 952 data_x added_binding_clauses"

definition added_bindings_system :: "(nat,nat,nat,nat) schema_system" where
  "added_bindings_system=add_view_definition added_binding_system 953 data_x (context_list_clauses 952 953)"

definition extension_formation_system :: "(nat,nat,nat,nat) schema_system" where
  "extension_formation_system=add_view_definition added_bindings_system 954 data_x {(0,extension_formation_schema)}"

lemma added_use_fresh_system_formed [simp]: "schema_system_formed added_use_fresh_system"
  unfolding added_use_fresh_system_def
  by (intro add_recursive_definition_formed[OF artifact_lookup_system_formed])
    (auto simp: added_use_fresh_schema_def schema_formed_def schema_dependencies_def single_valued_def
      rel_dom_def rel_ran_def octets_formed_def)

lemma added_use_fresh_definitions [simp]:
  "system_definitions added_use_fresh_system=insert 950 (system_definitions artifact_lookup_system)"
  by (simp add: added_use_fresh_system_def)

lemma added_uses_fresh_system_formed [simp]: "schema_system_formed added_uses_fresh_system"
  unfolding added_uses_fresh_system_def
  by (rule add_recursive_definition_formed[OF added_use_fresh_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma added_uses_fresh_definitions [simp]:
  "system_definitions added_uses_fresh_system=insert 951 (system_definitions added_use_fresh_system)"
  by (simp add: added_uses_fresh_system_def)

lemma added_binding_system_formed [simp]: "schema_system_formed added_binding_system"
  unfolding added_binding_system_def
  by (intro add_recursive_definition_formed[OF added_uses_fresh_system_formed])
    (auto simp: added_binding_clauses_def added_binding_added_schema_def added_binding_given_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma added_binding_definitions [simp]:
  "system_definitions added_binding_system=insert 952 (system_definitions added_uses_fresh_system)"
  by (simp add: added_binding_system_def)

lemma added_bindings_system_formed [simp]: "schema_system_formed added_bindings_system"
  unfolding added_bindings_system_def
  by (rule add_recursive_definition_formed[OF added_binding_system_formed])
    (auto simp: context_list_clauses_def context_list_nil_schema_def context_list_step_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma added_bindings_definitions [simp]:
  "system_definitions added_bindings_system=insert 953 (system_definitions added_binding_system)"
  by (simp add: added_bindings_system_def)

lemma extension_formation_system_formed [simp]: "schema_system_formed extension_formation_system"
  unfolding extension_formation_system_def
  by (intro add_recursive_definition_formed[OF added_bindings_system_formed])
    (auto simp: extension_formation_schema_def
      schema_formed_def schema_dependencies_def single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma extension_formation_definitions [simp]:
  "system_definitions extension_formation_system=insert 954 (system_definitions added_bindings_system)"
  by (simp add: extension_formation_system_def)

lemma extension_formation_call:
  "schema_call_formed extension_formation_system d t \<longleftrightarrow>
    d\<in>system_definitions extension_formation_system \<and> term_formed t"
proof -
  have fresh: "schema_call_formed added_use_fresh_system d t \<longleftrightarrow>
      d\<in>system_definitions added_use_fresh_system \<and> term_formed t" for d t
    using added_variable_calls[OF artifact_lookup_system_formed
      added_use_fresh_system_formed[unfolded added_use_fresh_system_def] artifact_lookup_call]
    by (simp only: added_use_fresh_system_def[symmetric])
  have freshes: "schema_call_formed added_uses_fresh_system d t \<longleftrightarrow>
      d\<in>system_definitions added_uses_fresh_system \<and> term_formed t" for d t
    using added_variable_calls[OF added_use_fresh_system_formed
      added_uses_fresh_system_formed[unfolded added_uses_fresh_system_def] fresh]
    by (simp only: added_uses_fresh_system_def[symmetric])
  have binding: "schema_call_formed added_binding_system d t \<longleftrightarrow>
      d\<in>system_definitions added_binding_system \<and> term_formed t" for d t
    using added_variable_calls[OF added_uses_fresh_system_formed
      added_binding_system_formed[unfolded added_binding_system_def] freshes]
    by (simp only: added_binding_system_def[symmetric])
  have bindings: "schema_call_formed added_bindings_system d t \<longleftrightarrow>
      d\<in>system_definitions added_bindings_system \<and> term_formed t" for d t
    using added_variable_calls[OF added_binding_system_formed
      added_bindings_system_formed[unfolded added_bindings_system_def] binding]
    by (simp only: added_bindings_system_def[symmetric])
  show ?thesis
    using added_variable_calls[OF added_bindings_system_formed
      extension_formation_system_formed[unfolded extension_formation_system_def] bindings]
    by (simp only: extension_formation_system_def[symmetric])
qed

lemma extension_formation_old_meaning:
  assumes member: "d\<in>system_definitions artifact_lookup_system"
  shows "(d,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (d,t)\<in>positive_meaning artifact_lookup_system"
proof -
  have fresh: "(d,t)\<in>positive_meaning added_use_fresh_system \<longleftrightarrow> (d,t)\<in>positive_meaning artifact_lookup_system"
    using added_definition_preserves_old(2)[OF artifact_lookup_system_formed
      added_use_fresh_system_formed[unfolded added_use_fresh_system_def], of d t] member
    by (auto simp: added_use_fresh_system_def)
  have freshes: "(d,t)\<in>positive_meaning added_uses_fresh_system \<longleftrightarrow> (d,t)\<in>positive_meaning added_use_fresh_system"
    using added_definition_preserves_old(2)[OF added_use_fresh_system_formed
      added_uses_fresh_system_formed[unfolded added_uses_fresh_system_def], of d t] member
    by (auto simp: added_uses_fresh_system_def)
  have binding: "(d,t)\<in>positive_meaning added_binding_system \<longleftrightarrow> (d,t)\<in>positive_meaning added_uses_fresh_system"
    using added_definition_preserves_old(2)[OF added_uses_fresh_system_formed
      added_binding_system_formed[unfolded added_binding_system_def], of d t] member
    by (auto simp: added_binding_system_def)
  have bindings: "(d,t)\<in>positive_meaning added_bindings_system \<longleftrightarrow> (d,t)\<in>positive_meaning added_binding_system"
    using added_definition_preserves_old(2)[OF added_binding_system_formed
      added_bindings_system_formed[unfolded added_bindings_system_def], of d t] member
    by (auto simp: added_bindings_system_def)
  have formation: "(d,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow>
      (d,t)\<in>positive_meaning added_bindings_system"
    using added_definition_preserves_old(2)[OF added_bindings_system_formed
      extension_formation_system_formed[unfolded extension_formation_system_def], of d t] member
    by (auto simp: extension_formation_system_def)
  show ?thesis using fresh freshes binding bindings formation by simp
qed

lemma extension_formation_components:
  "(20,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (20,t)\<in>positive_meaning keyed_list_system"
  "(21,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
  "(23,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (23,t)\<in>positive_meaning artifact_entries_system"
  "(24,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (24,t)\<in>positive_meaning binding_entries_system"
  "(26,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
  "(37,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
proof -
  have lower: "(d,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (d,t)\<in>positive_meaning binding_entries_system"
    if "d\<in>{20,21,23,24}" for d
  proof -
    have lookup: "d\<in>system_definitions artifact_lookup_system" "d\<in>system_definitions environment_identity_system"
      using that by auto
    show ?thesis
      using extension_formation_old_meaning[OF lookup(1), of t] artifact_lookup_environment_meaning[OF lookup(2), of t]
        environment_identity_previous_meaning[of d t] environment_admission_previous_meaning[of d t] that by auto
  qed
  show "(20,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (20,t)\<in>positive_meaning keyed_list_system"
    using lower[of 20] binding_entries_previous_meaning[of 20 t] binding_entry_keyed_meaning[of 20 t] by simp
  show "(21,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (21,t)\<in>positive_meaning keyed_list_system"
    using lower[of 21] binding_entries_previous_meaning[of 21 t] binding_entry_keyed_meaning[of 21 t] by simp
  show "(23,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (23,t)\<in>positive_meaning artifact_entries_system"
    using lower[of 23] binding_entries_previous_meaning[of 23 t] binding_entry_previous_meaning[of 23 t] by simp
  show "(24,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (24,t)\<in>positive_meaning binding_entries_system"
    using lower[of 24] by simp
  have members: "26\<in>system_definitions artifact_lookup_system" "37\<in>system_definitions artifact_lookup_system" by auto
  show "(26,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (\<exists>E. environment_value_presents E t)"
    using extension_formation_old_meaning[OF members(1), of t] artifact_lookup_components(1)[of t] by simp
  show "(37,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (37,t)\<in>positive_meaning artifact_lookup_system"
    by (rule extension_formation_old_meaning[OF members(2)])
qed

lemma extension_formation_families:
  "((950,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> c=0 \<and> S=added_use_fresh_schema"
  "((951,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 950 951"
  "((952,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> (c,S)\<in>added_binding_clauses"
  "((953,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 952 953"
  "((954,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> c=0 \<and> S=extension_formation_schema"
proof -
  have owned: "((d,c),S)\<in>system_clauses artifact_lookup_system \<Longrightarrow> d\<in>system_definitions artifact_lookup_system" for d c S
    using artifact_lookup_system_formed unfolding schema_system_formed_def by blast
  have absent: "((d,c),S)\<notin>system_clauses artifact_lookup_system" if "d\<in>{950,951,952,953,954}" for d c S
    using that by (auto dest: owned)
  show "((950,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> c=0 \<and> S=added_use_fresh_schema"
    "((951,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 950 951"
    "((952,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> (c,S)\<in>added_binding_clauses"
    "((953,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> (c,S)\<in>context_list_clauses 952 953"
    "((954,c),S)\<in>system_clauses extension_formation_system \<longleftrightarrow> c=0 \<and> S=extension_formation_schema"
    using absent by (auto simp: extension_formation_system_def added_bindings_system_def added_binding_system_def
      added_uses_fresh_system_def added_use_fresh_system_def)
qed

interpretation added_uses_fresh_lists: context_list_profile extension_formation_system 950 951
  by (rule context_list_profile.intro) (auto simp: extension_formation_call extension_formation_families)

interpretation added_bindings_lists: context_list_profile extension_formation_system 952 953
  by (rule context_list_profile.intro) (auto simp: extension_formation_call extension_formation_families)

subsection \<open>An added use is absent among the given's use keys\<close>

lemma added_use_fresh_rule:
  "(950,z)\<in>positive_meaning extension_formation_system \<longleftrightarrow>
    (\<exists>h. (\<forall>a\<in>schema_variables added_use_fresh_schema. term_formed (h a)) \<and>
      z=evaluate_pattern h (schema_conclusion added_use_fresh_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises added_use_fresh_schema \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning extension_formation_system))"
  by (rule variable_single_clause_valuation[OF extension_formation_system_formed extension_formation_families(1)])
    (simp_all add: added_use_fresh_schema_def extension_formation_call)

theorem added_use_fresh_exact:
  "(950,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (\<exists>xs k v.
    t=Pair_Term (pair_list_term xs) (Pair_Term k v) \<and> term_formed v \<and> term_formed k \<and> self_contained_term k \<and>
    formed_key_rows xs \<and> k\<notin>set (map fst xs))"
proof
  assume holds: "(950,t)\<in>positive_meaning extension_formation_system"
  obtain h where conclusion: "t=evaluate_pattern h (schema_conclusion added_use_fresh_schema)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises added_use_fresh_schema \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning extension_formation_system"
    using holds unfolding added_use_fresh_rule by blast
  have absent: "(20,Pair_Term (h 1) (h 0))\<in>positive_meaning keyed_list_system"
    using support by (auto simp: added_use_fresh_schema_def extension_formation_components)
  have formed: "term_formed (h 2)"
    using schema_call_formed_target[OF positive_meaning_formed[OF holds]] conclusion
    by (simp add: added_use_fresh_schema_def)
  show "\<exists>xs k v. t=Pair_Term (pair_list_term xs) (Pair_Term k v) \<and> term_formed v \<and> term_formed k \<and>
    self_contained_term k \<and> formed_key_rows xs \<and> k\<notin>set (map fst xs)"
    using absent formed conclusion by (auto simp: keyed_list_absence added_use_fresh_schema_def)
next
  assume "\<exists>xs k v. t=Pair_Term (pair_list_term xs) (Pair_Term k v) \<and> term_formed v \<and> term_formed k \<and>
    self_contained_term k \<and> formed_key_rows xs \<and> k\<notin>set (map fst xs)"
  then obtain xs k v where parts: "t=Pair_Term (pair_list_term xs) (Pair_Term k v)" "term_formed v"
    "term_formed k" "self_contained_term k" "formed_key_rows xs" "k\<notin>set (map fst xs)" by blast
  have absent: "(20,Pair_Term k (pair_list_term xs))\<in>positive_meaning extension_formation_system"
    using parts by (auto simp: extension_formation_components keyed_list_absence)
  have rows: "term_formed (pair_list_term xs)"
    using schema_call_formed_target[OF positive_meaning_formed[OF absent]] by simp
  let ?h="\<lambda>n::nat. if n=0 then pair_list_term xs else if n=1 then k else v"
  have result: "(950,evaluate_pattern ?h (schema_conclusion added_use_fresh_schema))
      \<in>positive_meaning extension_formation_system"
    unfolding added_use_fresh_rule by (rule exI[of _ ?h])
      (use parts rows absent in \<open>auto simp: added_use_fresh_schema_def schema_variables_def\<close>)
  show "(950,t)\<in>positive_meaning extension_formation_system"
    using result parts(1) by (simp add: added_use_fresh_schema_def)
qed

lemma list_all2_all_iff:
  assumes "list_all2 R xs ys" and "\<And>x y. R x y \<Longrightarrow> Q y \<longleftrightarrow> P x"
  shows "(\<forall>y\<in>set ys. Q y) \<longleftrightarrow> (\<forall>x\<in>set xs. P x)"
  using assms by (induction rule: list_all2_induct) auto

theorem added_uses_fresh_at_values:
  assumes given: "environment_value_presents E (Pair_Term a0 a1)"
    and rows: "data_collection_presents environment_artifact_entry_presents A y"
  shows "(951,Pair_Term a0 y)\<in>positive_meaning extension_formation_system \<longleftrightarrow> rel_dom A\<inter>environment_uses E={}"
proof -
  obtain ps b where e: "Pair_Term a0 a1=Pair_Term (pair_list_term ps) b" and keyed: "formed_key_rows ps"
    and uses: "\<And>w. use_data_term w\<in>set (map fst ps) \<longleftrightarrow> w\<in>environment_uses E"
    using environment_value_uses[OF given] by blast
  have a0: "a0=pair_list_term ps" using e by simp
  obtain xs ts where enumeration: "set xs=A" "list_all2 environment_artifact_entry_presents xs ts"
    "y=data_list_term ts"
    using rows unfolding data_collection_presents_def by blast
  have a0f: "term_formed a0" using environment_value_presents_formed[OF given] by simp
  have element: "(950,Pair_Term a0 x)\<in>positive_meaning extension_formation_system \<longleftrightarrow> fst z\<notin>environment_uses E"
    if read: "environment_artifact_entry_presents z x" for z x
  proof -
    obtain v where x: "x=Pair_Term (use_data_term (fst z)) v" and valued: "artifact_value_presents (snd z) v"
      using read unfolding environment_artifact_entry_presents_def by blast
    have vf: "term_formed v" using artifact_value_presents_formed[OF valued] by simp
    have key: "term_formed (use_data_term (fst z))" "self_contained_term (use_data_term (fst z))"
      using environment_artifact_entry_formed[OF read] x by simp_all
    show ?thesis unfolding added_use_fresh_exact using x vf key keyed uses[of "fst z"]
      by (auto simp: a0 pair_list_term_injective)
  qed
  have "(951,Pair_Term a0 y)\<in>positive_meaning extension_formation_system \<longleftrightarrow>
      (\<forall>x\<in>set ts. (950,Pair_Term a0 x)\<in>positive_meaning extension_formation_system)"
    using a0f by (auto simp: added_uses_fresh_lists.exact enumeration(3) data_list_term_injective)
  also have "\<dots> \<longleftrightarrow> (\<forall>z\<in>set xs. fst z\<notin>environment_uses E)"
    by (rule list_all2_all_iff[OF enumeration(2) element])
  also have "\<dots> \<longleftrightarrow> rel_dom A\<inter>environment_uses E={}"
    using enumeration(1) by (auto simp: rel_dom_def)
  finally show ?thesis .
qed

subsection \<open>An added binding is supported in the extension\<close>

theorem added_binding_raw:
  "(952,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> (\<exists>y g b. t=Pair_Term (Pair_Term y g) b \<and> term_formed g \<and>
    ((24,Pair_Term y b)\<in>positive_meaning binding_entries_system \<or>
     (\<exists>u k w a. b=Pair_Term (Pair_Term u k) w \<and>
       (24,Pair_Term y (Pair_Term (Pair_Term u k) u))\<in>positive_meaning binding_entries_system \<and>
       (37,Pair_Term g (Pair_Term w a))\<in>positive_meaning artifact_lookup_system)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume holds: ?lhs
  have consequence: "(952,t)\<in>schema_consequences extension_formation_system (positive_meaning extension_formation_system)"
    using holds positive_meaning_unfold[of extension_formation_system] by blast
  obtain c S f where clause: "((952,c),S)\<in>system_clauses extension_formation_system"
    and assignment: "\<forall>a\<in>schema_variables S. term_formed (f a)"
    and head: "t=evaluate_pattern f (schema_conclusion S)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning extension_formation_system"
    using schema_consequences_valuationD[OF consequence] by blast
  have schemas: "S=added_binding_added_schema \<or> S=added_binding_given_schema"
    using clause by (auto simp: extension_formation_families added_binding_clauses_def)
  then show ?rhs
  proof
    assume S: "S=added_binding_added_schema"
    have gf: "term_formed (f 1)" using assignment by (simp add: S added_binding_added_schema_def schema_variables_def)
    have p0: "(24,Pair_Term (f 0) (f 2))\<in>positive_meaning binding_entries_system"
      using support by (simp add: S added_binding_added_schema_def extension_formation_components)
    have t: "t=Pair_Term (Pair_Term (f 0) (f 1)) (f 2)" using head by (simp add: S added_binding_added_schema_def)
    show ?rhs using gf p0 t by blast
  next
    assume S: "S=added_binding_given_schema"
    have gf: "term_formed (f 1)" using assignment by (simp add: S added_binding_given_schema_def schema_variables_def)
    have p0: "(24,Pair_Term (f 0) (Pair_Term (Pair_Term (f 2) (f 3)) (f 2)))\<in>positive_meaning binding_entries_system"
      and p1: "(37,Pair_Term (f 1) (Pair_Term (f 4) (f 5)))\<in>positive_meaning artifact_lookup_system"
      using support by (simp_all add: S added_binding_given_schema_def extension_formation_components)
    have t: "t=Pair_Term (Pair_Term (f 0) (f 1)) (Pair_Term (Pair_Term (f 2) (f 3)) (f 4))"
      using head by (simp add: S added_binding_given_schema_def)
    show ?rhs using gf p0 p1 t by blast
  qed
next
  assume ?rhs
  then obtain y g b where t: "t=Pair_Term (Pair_Term y g) b" and gf: "term_formed g"
    and alternatives: "(24,Pair_Term y b)\<in>positive_meaning binding_entries_system \<or>
      (\<exists>u k w a. b=Pair_Term (Pair_Term u k) w \<and>
        (24,Pair_Term y (Pair_Term (Pair_Term u k) u))\<in>positive_meaning binding_entries_system \<and>
        (37,Pair_Term g (Pair_Term w a))\<in>positive_meaning artifact_lookup_system)" by blast
  from alternatives show ?lhs
  proof
    assume added: "(24,Pair_Term y b)\<in>positive_meaning binding_entries_system"
    have formed: "term_formed y" "term_formed b"
      using schema_call_formed_target[OF positive_meaning_formed[OF added]] by simp_all
    let ?f="\<lambda>n::nat. if n=0 then y else if n=1 then g else b"
    have "(952,evaluate_pattern ?f (schema_conclusion added_binding_added_schema))
        \<in>positive_meaning extension_formation_system"
      by (rule ordinary_positive_valuation_step[where c=0])
        (use formed gf added in \<open>auto simp: extension_formation_families added_binding_clauses_def
          added_binding_added_schema_def schema_variables_def extension_formation_call extension_formation_components\<close>)
    then show ?lhs using t by (simp add: added_binding_added_schema_def)
  next
    assume "\<exists>u k w a. b=Pair_Term (Pair_Term u k) w \<and>
      (24,Pair_Term y (Pair_Term (Pair_Term u k) u))\<in>positive_meaning binding_entries_system \<and>
      (37,Pair_Term g (Pair_Term w a))\<in>positive_meaning artifact_lookup_system"
    then obtain u k w a where b: "b=Pair_Term (Pair_Term u k) w"
      and source: "(24,Pair_Term y (Pair_Term (Pair_Term u k) u))\<in>positive_meaning binding_entries_system"
      and target: "(37,Pair_Term g (Pair_Term w a))\<in>positive_meaning artifact_lookup_system" by blast
    have formed: "term_formed y" "term_formed u" "term_formed k" "term_formed w" "term_formed a"
      using schema_call_formed_target[OF positive_meaning_formed[OF source]]
        schema_call_formed_target[OF positive_meaning_formed[OF target]] by simp_all
    let ?f="\<lambda>n::nat. if n=0 then y else if n=1 then g else if n=2 then u else if n=3 then k
      else if n=4 then w else a"
    have "(952,evaluate_pattern ?f (schema_conclusion added_binding_given_schema))
        \<in>positive_meaning extension_formation_system"
      by (rule ordinary_positive_valuation_step[where c=1])
        (use formed gf source target in \<open>auto simp: extension_formation_families added_binding_clauses_def
          added_binding_given_schema_def schema_variables_def extension_formation_call extension_formation_components\<close>)
    then show ?lhs using t b by (simp add: added_binding_given_schema_def)
  qed
qed

lemma added_binding_data:
  assumes holds: "(952,Pair_Term (Pair_Term y g) b)\<in>positive_meaning extension_formation_system"
    and rows: "data_collection_presents environment_artifact_entry_presents A y"
  shows "\<exists>z. b=binding_data z"
proof -
  have "(24,Pair_Term y b)\<in>positive_meaning binding_entries_system \<or>
    (\<exists>u k w a. b=Pair_Term (Pair_Term u k) w \<and>
      (24,Pair_Term y (Pair_Term (Pair_Term u k) u))\<in>positive_meaning binding_entries_system \<and>
      (37,Pair_Term g (Pair_Term w a))\<in>positive_meaning artifact_lookup_system)"
    using holds unfolding added_binding_raw by auto
  then show ?thesis
  proof
    assume "(24,Pair_Term y b)\<in>positive_meaning binding_entries_system"
    then show ?thesis using binding_entries_element[OF rows] by blast
  next
    assume "\<exists>u k w a. b=Pair_Term (Pair_Term u k) w \<and>
      (24,Pair_Term y (Pair_Term (Pair_Term u k) u))\<in>positive_meaning binding_entries_system \<and>
      (37,Pair_Term g (Pair_Term w a))\<in>positive_meaning artifact_lookup_system"
    then obtain u k w a where b: "b=Pair_Term (Pair_Term u k) w"
      and source: "(24,Pair_Term y (Pair_Term (Pair_Term u k) u))\<in>positive_meaning binding_entries_system"
      and target: "(37,Pair_Term g (Pair_Term w a))\<in>positive_meaning artifact_lookup_system" by blast
    obtain z where z: "Pair_Term (Pair_Term u k) u=binding_data z" using source binding_entries_element[OF rows] by blast
    obtain x where x: "w=use_data_term x" using target by (auto simp: artifact_lookup_exact)
    have "b=binding_data ((fst (fst z),snd (fst z)),x)" using b z x by (simp add: binding_data_def)
    then show ?thesis by blast
  qed
qed

theorem added_binding_at_values:
  assumes rows: "data_collection_presents environment_artifact_entry_presents A y"
    and given: "environment_value_presents E g"
  shows "(952,Pair_Term (Pair_Term y g) (binding_data z))\<in>positive_meaning extension_formation_system \<longleftrightarrow>
    (\<exists>R. (fst (fst z),R)\<in>A \<and> snd (fst z)\<in>rra_carrier (object_structure R)) \<and>
      snd z\<in>rel_dom A \<union> environment_uses E"
proof -
  have gf: "term_formed g" and ef: "environment_formed E" using environment_value_presents_formed[OF given] by auto
  obtain u k v where z: "z=((u,k),v)" by (metis prod.collapse)
  have b: "binding_data z=Pair_Term (Pair_Term (use_data_term u) (Payload_Term k)) (use_data_term v)"
    by (simp add: z binding_data_def)
  have lookup: "(\<exists>a. (37,Pair_Term g (Pair_Term (use_data_term w) a))\<in>positive_meaning artifact_lookup_system) \<longleftrightarrow>
      w\<in>environment_uses E" for w
  proof
    assume "\<exists>a. (37,Pair_Term g (Pair_Term (use_data_term w) a))\<in>positive_meaning artifact_lookup_system"
    then obtain E' x R where other: "environment_value_presents E' g" "use_data_term w=use_data_term x" "artifact_at E' x R"
      by (auto simp: artifact_lookup_exact)
    have "E'=E" by (rule environment_value_presents_unique[OF other(1) given])
    moreover have "x=w" using injD[OF use_data_term_injective other(2)] by simp
    ultimately show "w\<in>environment_uses E" using other(3) by (auto simp: artifact_at_def environment_uses_def rel_dom_def)
  next
    assume "w\<in>environment_uses E"
    then obtain R where row: "artifact_at E w R" by (auto simp: artifact_at_def environment_uses_def rel_dom_def)
    have "exact_formed R" using ef row by (simp add: environment_formed_def)
    then obtain a where "artifact_value_presents R a" using artifact_value_presents_total by blast
    then show "\<exists>a. (37,Pair_Term g (Pair_Term (use_data_term w) a))\<in>positive_meaning artifact_lookup_system"
      using given row by (auto simp: artifact_lookup_exact)
  qed
  have source: "(24,Pair_Term y (Pair_Term (Pair_Term (use_data_term u) (Payload_Term k)) (use_data_term u)))
      \<in>positive_meaning binding_entries_system \<longleftrightarrow> (\<exists>R. (u,R)\<in>A \<and> k\<in>rra_carrier (object_structure R))"
  proof -
    have "(24,Pair_Term y (binding_data ((u,k),u)))\<in>positive_meaning binding_entries_system \<longleftrightarrow>
        binding_supported A ((u,k),u)"
      using binding_entries_element[OF rows, of "binding_data ((u,k),u)"] by (auto simp: inj_eq[OF binding_data_injective])
    then show ?thesis by (auto simp: binding_data_def rel_dom_def)
  qed
  have supported: "(24,Pair_Term y (binding_data z))\<in>positive_meaning binding_entries_system \<longleftrightarrow>
      (\<exists>R. (u,R)\<in>A \<and> k\<in>rra_carrier (object_structure R)) \<and> v\<in>rel_dom A"
    using binding_entries_element[OF rows, of "binding_data z"] by (auto simp: inj_eq[OF binding_data_injective] z)
  have raw: "(952,Pair_Term (Pair_Term y g) (binding_data z))\<in>positive_meaning extension_formation_system \<longleftrightarrow>
      (24,Pair_Term y (binding_data z))\<in>positive_meaning binding_entries_system \<or>
      ((24,Pair_Term y (Pair_Term (Pair_Term (use_data_term u) (Payload_Term k)) (use_data_term u)))
          \<in>positive_meaning binding_entries_system \<and>
        (\<exists>a. (37,Pair_Term g (Pair_Term (use_data_term v) a))\<in>positive_meaning artifact_lookup_system))"
    unfolding added_binding_raw using gf by (auto simp: b)
  show ?thesis unfolding raw supported source lookup using z by auto
qed

theorem added_bindings_at_values:
  assumes rows: "data_collection_presents environment_artifact_entry_presents A y"
    and given: "environment_value_presents E g"
  shows "(953,Pair_Term (Pair_Term y g) (data_list_term (map binding_data zs)))\<in>positive_meaning extension_formation_system
    \<longleftrightarrow> (\<forall>z\<in>set zs. (\<exists>R. (fst (fst z),R)\<in>A \<and> snd (fst z)\<in>rra_carrier (object_structure R)) \<and>
      snd z\<in>rel_dom A \<union> environment_uses E)"
proof -
  have yf: "term_formed y" by (rule data_collection_presents_formed[OF rows]) (meson environment_artifact_entry_formed)
  have gf: "term_formed g" using environment_value_presents_formed[OF given] by simp
  show ?thesis using yf gf
    by (auto simp: added_bindings_lists.exact data_list_term_injective added_binding_at_values[OF rows given])
qed

lemma binding_rows_keyed:
  assumes data: "data_elements (map binding_data zs)"
  shows "(21,data_list_term (map binding_data zs))\<in>positive_meaning keyed_list_system \<longleftrightarrow>
    distinct zs \<and> single_valued (set zs)"
proof -
  have injective: "inj (case_prod site_data_term)"
    by (rule injI; rename_tac z w; case_tac z; case_tac w) simp
  show ?thesis
  proof (rule keyed_list_encoded_keys[OF _ data injective])
    show "list_all2 (\<lambda>z t. t=binding_data z) zs (map binding_data zs)" by (simp add: list_all2_function)
  next
    fix z t assume "t=binding_data z"
    then show "\<exists>v. t=Pair_Term (case_prod site_data_term (fst z)) v"
      by (auto simp: binding_data_def site_data_term_def split: prod.splits)
  qed
qed

subsection \<open>The extension's formation\<close>

abbreviation extension_formation_result :: "factor_term \<Rightarrow> bool" where
  "extension_formation_result t \<equiv> \<exists>E e A B p w. t=Pair_Term e (Pair_Term p w) \<and>
    environment_value_presents E e \<and> environment_rows_presents (A,B) p \<and> term_formed w \<and>
    environment_additions E A B \<and> environment_formed (environment_extension E A B)"

lemma extension_formation_rule:
  "(954,z)\<in>positive_meaning extension_formation_system \<longleftrightarrow>
    (\<exists>h. (\<forall>a\<in>schema_variables extension_formation_schema. term_formed (h a)) \<and>
      z=evaluate_pattern h (schema_conclusion extension_formation_schema) \<and>
      (\<forall>s d p. (s,d,p)\<in>schema_premises extension_formation_schema \<longrightarrow>
        (d,evaluate_pattern h p)\<in>positive_meaning extension_formation_system))"
  by (rule variable_single_clause_valuation[OF extension_formation_system_formed extension_formation_families(5)])
    (simp_all add: extension_formation_schema_def extension_formation_call)

theorem extension_formation_exact:
  "(954,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> extension_formation_result t"
proof
  assume holds: "(954,t)\<in>positive_meaning extension_formation_system"
  obtain h where assignment: "\<forall>a\<in>schema_variables extension_formation_schema. term_formed (h a)"
    and head: "t=evaluate_pattern h (schema_conclusion extension_formation_schema)"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises extension_formation_schema \<longrightarrow>
      (d,evaluate_pattern h p)\<in>positive_meaning extension_formation_system"
    using holds unfolding extension_formation_rule by blast
  have t: "t=Pair_Term (Pair_Term (h 0) (h 1)) (Pair_Term (Pair_Term (h 2) (h 3)) (h 4))"
    using head by (simp add: extension_formation_schema_def)
  have wf: "term_formed (h 4)"
    using assignment by (simp add: extension_formation_schema_def schema_variables_def)
  have given: "(26,Pair_Term (h 0) (h 1))\<in>positive_meaning extension_formation_system"
    and rows: "(23,h 2)\<in>positive_meaning extension_formation_system" "(21,h 2)\<in>positive_meaning extension_formation_system"
    and fresh: "(951,Pair_Term (h 0) (h 2))\<in>positive_meaning extension_formation_system"
    and keys: "(21,h 3)\<in>positive_meaning extension_formation_system"
    and bindings: "(953,Pair_Term (Pair_Term (h 2) (Pair_Term (h 0) (h 1))) (h 3))\<in>positive_meaning extension_formation_system"
    using support by (auto simp: extension_formation_schema_def)
  obtain E where ge: "environment_value_presents E (Pair_Term (h 0) (h 1))"
    using given by (auto simp: extension_formation_components)
  obtain A where ra: "data_collection_presents environment_artifact_entry_presents A (h 2)" and svA: "single_valued A"
    using rows admitted_artifact_table[of "h 2"] by (auto simp: extension_formation_components)
  have fa: "finite A" and entries: "\<And>u R. (u,R)\<in>A \<Longrightarrow> exact_formed R" using entry_collection_rows[OF ra] by blast+
  have disjoint: "rel_dom A\<inter>environment_uses E={}" using fresh added_uses_fresh_at_values[OF ge ra] by simp
  obtain bs where bs: "h 3=data_list_term bs"
    and each: "\<forall>b\<in>set bs. (952,Pair_Term (Pair_Term (h 2) (Pair_Term (h 0) (h 1))) b)\<in>positive_meaning extension_formation_system"
    using bindings by (auto simp: added_bindings_lists.exact)
  have "\<forall>b\<in>set bs. \<exists>z. b=binding_data z" using each added_binding_data[OF _ ra] by blast
  then have "\<exists>zs. bs=map binding_data zs" unfolding list_range_witnesses[symmetric] .
  then obtain zs where zs: "bs=map binding_data zs" by blast
  have formed_rows: "term_formed (binding_data z)" if member: "z\<in>set zs" for z
  proof -
    have "(952,Pair_Term (Pair_Term (h 2) (Pair_Term (h 0) (h 1))) (binding_data z))\<in>positive_meaning extension_formation_system"
      using each zs member by auto
    from schema_call_formed_target[OF positive_meaning_formed[OF this]] show ?thesis by simp
  qed
  have data: "data_elements (map binding_data zs)" using formed_rows by auto
  have unique: "distinct zs \<and> single_valued (set zs)"
    using keys binding_rows_keyed[OF data] bs zs by (simp add: extension_formation_components)
  have supported: "\<forall>z\<in>set zs. (\<exists>R. (fst (fst z),R)\<in>A \<and> snd (fst z)\<in>rra_carrier (object_structure R)) \<and>
      snd z\<in>rel_dom A \<union> environment_uses E"
    using bindings added_bindings_at_values[OF ra ge, of zs] bs zs by simp
  have additions: "environment_additions E A (set zs)"
    using environment_value_presents_formed[OF ge] fa disjoint supported
    by (auto simp: environment_additions_def rel_dom_def)
  have formed: "environment_formed (environment_extension E A (set zs))"
    using environment_extension_formed_iff[OF additions] svA entries unique supported by auto
  have rows_presents: "environment_rows_presents (A,set zs) (Pair_Term (h 2) (h 3))"
    using ra unique bs zs by (auto simp: environment_rows_presents_def data_collection_presents_function)
  show "extension_formation_result t" using t ge rows_presents wf additions formed by blast
next
  assume "extension_formation_result t"
  then obtain E e A B p w where t: "t=Pair_Term e (Pair_Term p w)" and ge: "environment_value_presents E e"
    and rp: "environment_rows_presents (A,B) p" and wf: "term_formed w"
    and additions: "environment_additions E A B" and formed: "environment_formed (environment_extension E A B)"
    by blast
  have conditions: "single_valued A" "single_valued B"
    "\<forall>z\<in>B. (\<exists>R. (fst (fst z),R)\<in>A \<and> snd (fst z)\<in>rra_carrier (object_structure R)) \<and>
      snd z\<in>rel_dom A \<union> environment_uses E"
    using formed environment_extension_formed_iff[OF additions] by auto
  have disjoint: "rel_dom A\<inter>environment_uses E={}" using additions by (simp add: environment_additions_def)
  obtain a0 a1 where e: "e=Pair_Term a0 a1" using ge unfolding environment_value_presents_def by blast
  have ge': "environment_value_presents E (Pair_Term a0 a1)" using ge e by simp
  obtain ra rb where p: "p=Pair_Term ra rb" and ra: "data_collection_presents environment_artifact_entry_presents A ra"
    and rb: "data_collection_presents (\<lambda>z v. v=binding_data z) B rb"
    using rp unfolding environment_rows_presents_def by auto
  obtain zs where zs: "distinct zs" "set zs=B" "rb=data_list_term (map binding_data zs)"
    using rb by (auto simp: data_collection_presents_function)
  have zf: "term_formed (binding_data z)" if "z\<in>B" for z
    using binding_data_formed[OF formed, of z] that by simp
  have data: "data_elements (map binding_data zs)" using zf zs by auto
  have af: "term_formed a0" "term_formed a1" using environment_value_presents_formed[OF ge'] by simp_all
  have raf: "term_formed ra" by (rule data_collection_presents_formed[OF ra]) (meson environment_artifact_entry_formed)
  have rbf: "term_formed rb" using data zs(3) by (simp add: data_list_term_formed)
  have calls: "(26,Pair_Term a0 a1)\<in>positive_meaning extension_formation_system"
    "(23,ra)\<in>positive_meaning extension_formation_system" "(21,ra)\<in>positive_meaning extension_formation_system"
    "(951,Pair_Term a0 ra)\<in>positive_meaning extension_formation_system"
    "(21,rb)\<in>positive_meaning extension_formation_system"
    "(953,Pair_Term (Pair_Term ra (Pair_Term a0 a1)) rb)\<in>positive_meaning extension_formation_system"
    using ge' admitted_artifact_table[of ra] ra conditions(1) added_uses_fresh_at_values[OF ge' ra] disjoint
      binding_rows_keyed[OF data] zs conditions(2) added_bindings_at_values[OF ra ge', of zs] conditions(3)
    by (auto simp: extension_formation_components)
  let ?h="\<lambda>n::nat. if n=0 then a0 else if n=1 then a1 else if n=2 then ra else if n=3 then rb else w"
  have result: "(954,evaluate_pattern ?h (schema_conclusion extension_formation_schema))
      \<in>positive_meaning extension_formation_system"
    unfolding extension_formation_rule by (rule exI[of _ ?h])
      (use calls af raf rbf wf in \<open>auto simp: extension_formation_schema_def schema_variables_def\<close>)
  show "(954,t)\<in>positive_meaning extension_formation_system"
    using result t e p by (simp add: extension_formation_schema_def)
qed

subsection \<open>G1 is exact to environment inclusion at the given and the extension\<close>

corollary extension_formation_inclusion:
  assumes given: "environment_value_presents E e" and rows: "environment_rows_presents (A,B) p"
    and additions: "environment_additions E A B" and site: "term_formed w"
  shows "(954,Pair_Term e (Pair_Term p w))\<in>positive_meaning extension_formation_system \<longleftrightarrow>
    (\<exists>f. environment_value_presents (environment_extension E A B) f \<and>
      (113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system)"
proof
  assume "(954,Pair_Term e (Pair_Term p w))\<in>positive_meaning extension_formation_system"
  then obtain E' A' B' where other: "environment_value_presents E' e" "environment_rows_presents (A',B') p"
    and formed: "environment_formed (environment_extension E' A' B')"
    unfolding extension_formation_exact by blast
  have "E'=E" by (rule environment_value_presents_unique[OF other(1) given])
  moreover have "(A',B')=(A,B)" by (rule environment_rows_unique[OF other(2) rows])
  ultimately have ext: "environment_formed (environment_extension E A B)" using formed by simp
  obtain f where f: "environment_value_presents (environment_extension E A B) f"
    using environment_value_presents_total[OF ext] by blast
  have "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
    unfolding environment_inclusion_exact using given f environment_extension_included by blast
  then show "\<exists>f. environment_value_presents (environment_extension E A B) f \<and>
      (113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system" using f by blast
next
  assume "\<exists>f. environment_value_presents (environment_extension E A B) f \<and>
      (113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
  then obtain f where "environment_value_presents (environment_extension E A B) f" by blast
  then have "environment_formed (environment_extension E A B)" using environment_value_presents_formed by blast
  then show "(954,Pair_Term e (Pair_Term p w))\<in>positive_meaning extension_formation_system"
    unfolding extension_formation_exact using given rows site additions by blast
qed

corollary extension_formation_on_additions:
  assumes given: "environment_value_presents E e" and presented: "additions_presents E (F,s) a"
    and candidate: "environment_value_presents F f"
  shows "(954,Pair_Term e a)\<in>positive_meaning extension_formation_system"
    and "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
proof -
  have domain: "additions_domain E (F,s)" and valued: "additions_value_presents (added_rows E F,s) a"
    using presented by (simp_all add: additions_presents_def)
  obtain p where p: "environment_rows_presents (added_rows E F) p" "a=Pair_Term p (site_data_term (fst s) (snd s))"
    using valued unfolding additions_value_presents_def by auto
  have additions: "environment_additions E (fst (added_rows E F)) (snd (added_rows E F))"
    and extension: "F=environment_extension E (fst (added_rows E F)) (snd (added_rows E F))"
    using additions_domain_extension[OF domain] by blast+
  have included: "environment_included E F" and position: "s\<in>environment_positions F"
    using domain by (simp_all add: additions_domain_def)
  have "site_value_presents F (fst s) (snd s) (Pair_Term f (site_data_term (fst s) (snd s)))"
    using candidate position by (auto simp: site_value_presents_def)
  then have site: "term_formed (site_data_term (fst s) (snd s))" using site_value_presents_formed by fastforce
  have formed: "environment_formed (environment_extension E (fst (added_rows E F)) (snd (added_rows E F)))"
    using environment_value_presents_formed[OF candidate] extension by simp
  have rows: "environment_rows_presents (fst (added_rows E F),snd (added_rows E F)) p" using p(1) by simp
  show "(954,Pair_Term e a)\<in>positive_meaning extension_formation_system"
    unfolding extension_formation_exact using given rows site additions formed p(2) by blast
  show "(113,Pair_Term e f)\<in>positive_meaning environment_inclusion_system"
    unfolding environment_inclusion_exact using given candidate included by blast
qed

section \<open>The additions' use action\<close>

text \<open>
  A permutation of uses acts on the given environment by @{const rename_environment} and on the additions by
  the same action on their two tables and by the site action on their site
  (@{thm [source] site_renaming_action}). The class relative to a given is closed under that action on the
  given and the extension together, environment inclusion's clause
  (@{thm [source] environment_inclusion_equivariant}) keeping the inclusion. G1's relation is equivariant,
  and its presented form is invariant along every renaming correspondence of the pair of the given's value
  and the additions (@{thm [source] presented_observation_renaming}).
\<close>

definition additions_tables ::
  "(('u\<times>exact_artifact) set \<times> (('u\<times>local_address)\<times>'u) set) \<times> ('u\<times>local_address) \<Rightarrow> 'u artifact_environment" where
  "additions_tables z=\<lparr>environment_artifacts=fst (fst z),environment_bindings=snd (fst z)\<rparr>"

definition additions_renaming ::
  "('u \<Rightarrow> 'u) \<Rightarrow> (('u\<times>exact_artifact) set \<times> (('u\<times>local_address)\<times>'u) set) \<times> ('u\<times>local_address) \<Rightarrow>
    (('u\<times>exact_artifact) set \<times> (('u\<times>local_address)\<times>'u) set) \<times> ('u\<times>local_address)" where
  "additions_renaming h z=
    ((environment_artifacts (rename_environment h (additions_tables z)),
      environment_bindings (rename_environment h (additions_tables z))),map_prod h id (snd z))"

lemma additions_renaming_fields [simp]:
  "additions_renaming h ((A,B),s)=
    (((\<lambda>(u,R). (h u,R)) ` A,(\<lambda>((u,k),v). ((h u,k),h v)) ` B),(h (fst s),snd s))"
  by (cases s) (simp add: additions_renaming_def additions_tables_def rename_environment_def)

lemma additions_tables_renaming:
  "additions_tables (additions_renaming h z)=rename_environment h (additions_tables z)"
  by (simp add: additions_renaming_def additions_tables_def rename_environment_def)

lemma environment_fields_eta [simp]:
  "\<lparr>environment_artifacts=environment_artifacts X,environment_bindings=environment_bindings X\<rparr>=X"
  by (cases X) simp

lemma additions_tables_determine:
  assumes "additions_tables x=additions_tables y" and "snd x=snd y"
  shows "x=y"
  using assms by (simp add: additions_tables_def prod_eq_iff)

definition additions_data_domain ::
  "(('u\<times>exact_artifact) set \<times> (('u\<times>local_address)\<times>'u) set) \<times> ('u\<times>local_address) \<Rightarrow> bool" where
  "additions_data_domain z \<longleftrightarrow> finite (fst (fst z)) \<and> finite (snd (fst z)) \<and>
    (\<forall>u R. (u,R)\<in>fst (fst z) \<longrightarrow> exact_formed R)"

theorem additions_renaming_action: "renaming_action bij additions_renaming additions_data_domain"
proof (rule renaming_action.intro, goal_cases)
  case (1 h) then show ?case .
next
  case 2 show ?case by simp
next
  case (3 g h) then show ?case using bij_comp by blast
next
  case (4 h) then show ?case by (rule bij_imp_bij_inv)
next
  case (5 h a)
  obtain A B s where a: "a=((A,B),s)" by (metis prod.collapse)
  show ?case using 5(2) by (auto simp: a additions_data_domain_def)
next
  case (6 a)
  show ?case
    by (rule additions_tables_determine)
      (simp_all add: additions_tables_renaming additions_renaming_def additions_tables_def prod.map_id)
next
  case (7 g h a)
  show ?case
    by (rule additions_tables_determine)
      (simp_all add: additions_tables_renaming rename_environment_comp additions_renaming_def prod.map_comp
        additions_tables_def)
qed

lemma environment_formed_renaming_iff:
  assumes permutation: "bij h"
  shows "environment_formed (rename_environment h F) \<longleftrightarrow> environment_formed F"
proof
  assume formed: "environment_formed (rename_environment h F)"
  have "rename_environment (inv h) (rename_environment h F)=F"
    by (simp add: rename_environment_comp[symmetric] inv_o_cancel[OF bij_is_inj[OF permutation]])
  moreover have "environment_formed (rename_environment (inv h) (rename_environment h F))"
    by (rule environment_renaming_formed[OF formed bij_is_inj[OF bij_imp_bij_inv[OF permutation]]])
  ultimately show "environment_formed F" by simp
next
  assume "environment_formed F"
  then show "environment_formed (rename_environment h F)" by (rule environment_renaming_formed[OF _ bij_is_inj[OF permutation]])
qed

lemma environment_extension_renaming:
  "rename_environment h (environment_extension E A B)=
    environment_extension (rename_environment h E) ((\<lambda>(u,R). (h u,R)) ` A) ((\<lambda>((u,k),v). ((h u,k),h v)) ` B)"
  by (simp add: rename_environment_def environment_extension_def merge_environment_def image_Un)

lemma environment_additions_renaming:
  assumes permutation: "bij h"
  shows "environment_additions (rename_environment h E) ((\<lambda>(u,R). (h u,R)) ` A) ((\<lambda>((u,k),v). ((h u,k),h v)) ` B)
    \<longleftrightarrow> environment_additions E A B"
proof -
  have injective: "inj h" using bij_is_inj[OF permutation] .
  have rows: "inj (\<lambda>(u,R). (h u,R))" using injective by (auto intro!: injI split: prod.splits simp: inj_eq)
  have bindings: "inj (\<lambda>((u,k),v). ((h u,k),h v))" using injective by (auto intro!: injI split: prod.splits simp: inj_eq)
  have domain: "rel_dom ((\<lambda>(u,R). (h u,R)) ` A)=h ` rel_dom A" by (force simp: rel_dom_def)
  have apart: "h ` rel_dom A \<inter> h ` environment_uses E={} \<longleftrightarrow> rel_dom A \<inter> environment_uses E={}"
    by (simp add: image_Int[OF injective, symmetric])
  have sources: "(\<forall>z\<in>(\<lambda>((u,k),v). ((h u,k),h v)) ` B. fst (fst z)\<in>h ` rel_dom A) \<longleftrightarrow>
      (\<forall>z\<in>B. fst (fst z)\<in>rel_dom A)"
  proof
    assume left: "\<forall>z\<in>(\<lambda>((u,k),v). ((h u,k),h v)) ` B. fst (fst z)\<in>h ` rel_dom A"
    show "\<forall>z\<in>B. fst (fst z)\<in>rel_dom A"
    proof
      fix z assume member: "z\<in>B"
      obtain u k v where z: "z=((u,k),v)" by (metis prod.collapse)
      have "((h u,k),h v)\<in>(\<lambda>((u,k),v). ((h u,k),h v)) ` B" using member z by force
      then have "h u\<in>h ` rel_dom A" using left by fastforce
      then show "fst (fst z)\<in>rel_dom A" using z inj_image_mem_iff[OF injective] by simp
    qed
  next
    assume "\<forall>z\<in>B. fst (fst z)\<in>rel_dom A"
    then show "\<forall>z\<in>(\<lambda>((u,k),v). ((h u,k),h v)) ` B. fst (fst z)\<in>h ` rel_dom A" by (force split: prod.splits)
  qed
  show ?thesis
    by (simp only: environment_additions_def environment_formed_renaming_iff[OF permutation]
      finite_image_iff[OF inj_on_subset[OF rows subset_UNIV]] finite_image_iff[OF inj_on_subset[OF bindings subset_UNIV]]
      domain environment_renaming_uses apart sources)
qed

subsection \<open>The class relative to a given is closed under the action\<close>

abbreviation additions_domain_renaming where
  "additions_domain_renaming \<equiv> product_action rename_environment
    (product_action rename_environment (\<lambda>h. map_prod h id))"

theorem additions_domain_renaming_action:
  "renaming_action bij additions_domain_renaming (\<lambda>z. additions_domain (fst z) (snd z))"
proof -
  have both: "renaming_action bij additions_domain_renaming
      (\<lambda>z. environment_formed (fst z) \<and> (environment_formed (fst (snd z)) \<and> True))"
    by (rule renaming_action_product[OF environment_renaming_action
      renaming_action_product[OF environment_renaming_action site_renaming_action]])
  show ?thesis
  proof (rule renaming_action_subdomain[OF both], goal_cases)
    case (1 z)
    then show ?case by (simp add: additions_domain_def)
  next
    case (2 h z)
    then have permutation: "bij h" and domain: "additions_domain (fst z) (snd z)" by simp_all
    obtain E F s where z: "z=(E,(F,s))" by (metis prod.collapse)
    have injective: "inj h" using bij_is_inj[OF permutation] .
    have ef: "environment_formed E" and ff: "environment_formed F" and included: "environment_included E F"
      and outside: "\<forall>b\<in>environment_bindings F-environment_bindings E. fst (fst b)\<notin>environment_uses E"
      and site: "s\<in>environment_positions F"
      using domain z by (simp_all add: additions_domain_def)
    have kept: "environment_included (rename_environment h E) (rename_environment h F)"
      using environment_inclusion_equivariant[unfolded renaming_equivariant_def, rule_format, of h "(E,F)"]
        permutation ef ff included by simp
    have bindings: "inj (\<lambda>((u,k),v). ((h u,k),h v))" using injective by (auto intro!: injI split: prod.splits simp: inj_eq)
    have difference: "environment_bindings (rename_environment h F)-environment_bindings (rename_environment h E)=
        (\<lambda>((u,k),v). ((h u,k),h v)) ` (environment_bindings F-environment_bindings E)"
      by (simp add: rename_environment_def image_set_diff[OF bindings])
    have sources: "\<forall>b\<in>environment_bindings (rename_environment h F)-environment_bindings (rename_environment h E).
        fst (fst b)\<notin>environment_uses (rename_environment h E)"
      unfolding difference environment_renaming_uses
    proof
      fix b assume "b\<in>(\<lambda>((u,k),v). ((h u,k),h v)) ` (environment_bindings F-environment_bindings E)"
      then obtain b0 where b0: "b0\<in>environment_bindings F-environment_bindings E"
        and b: "b=(\<lambda>((u,k),v). ((h u,k),h v)) b0" by blast
      obtain u k v where parts: "b0=((u,k),v)" by (metis prod.collapse)
      have "u\<notin>environment_uses E" using outside[rule_format, OF b0] parts by simp
      moreover have "fst (fst b)=h u" using b parts by simp
      ultimately show "fst (fst b)\<notin>h ` environment_uses E" using inj_image_mem_iff[OF injective] by simp
    qed
    have position: "map_prod h id s\<in>environment_positions (rename_environment h F)"
      using site by (simp add: environment_positions_renaming)
    show ?case
      using environment_renaming_formed[OF ef injective] environment_renaming_formed[OF ff injective]
        kept sources position
      by (simp add: z additions_domain_def product_action_def)
  qed
qed

subsection \<open>G1's relation is equivariant\<close>

definition additions_pair_presents ::
  "local_address option artifact_environment \<times>
    (((local_address option\<times>exact_artifact) set \<times> ((local_address option\<times>local_address)\<times>local_address option) set)
      \<times> (local_address option\<times>local_address)) \<Rightarrow> factor_term \<Rightarrow> bool" where
  "additions_pair_presents=factor_pair_presents environment_value_presents additions_value_presents"

abbreviation additions_pair_domain where
  "additions_pair_domain x \<equiv> environment_formed (fst x) \<and> additions_data_domain (snd x)"

lemma environment_rows_domain:
  assumes rows: "environment_rows_presents (A,B) p"
  shows "additions_data_domain ((A,B),s)"
proof -
  obtain a b where parts: "data_collection_presents environment_artifact_entry_presents A a"
    "data_collection_presents (\<lambda>z v. v=binding_data z) B b"
    using rows unfolding environment_rows_presents_def by auto
  have "finite B" using parts(2) unfolding data_collection_presents_def by auto
  then show ?thesis using entry_collection_rows[OF parts(1)] by (simp add: additions_data_domain_def)
qed

theorem additions_pair_presentation_class:
  "presentation_class additions_pair_presents additions_pair_domain (\<lambda>t. \<exists>x. additions_pair_presents x t)"
proof (rule presentation_class.intro, goal_cases)
  case (1 x t)
  then obtain e a p where e: "environment_value_presents (fst x) e"
    and p: "environment_rows_presents (fst (snd x)) p"
    unfolding additions_pair_presents_def factor_pair_presents_def additions_value_presents_def by blast
  show "additions_pair_domain x"
    using environment_value_presents_formed[OF e] environment_rows_domain[of "fst (fst (snd x))" "snd (fst (snd x))" p "snd (snd x)"] p
    by simp
next
  case (2 x t) then show ?case by blast
next
  case (3 x)
  then have domain: "additions_pair_domain x" by simp
  obtain e where e: "environment_value_presents (fst x) e" using environment_value_presents_total domain by blast
  obtain p where p: "environment_rows_presents (fst (fst (snd x)),snd (fst (snd x))) p"
    using environment_rows_total[of "fst (fst (snd x))" "snd (fst (snd x))"] domain
    by (auto simp: additions_data_domain_def)
  show ?case
    using e p by (auto simp: additions_pair_presents_def factor_pair_presents_def additions_value_presents_def)
next
  case (4 t) then show ?case .
next
  case (5 x t y)
  then have first: "additions_pair_presents x t" and second: "additions_pair_presents y t" by simp_all
  obtain e a where left: "environment_value_presents (fst x) e" "additions_value_presents (snd x) a" "t=Pair_Term e a"
    using first unfolding additions_pair_presents_def factor_pair_presents_def by blast
  obtain e' a' where right: "environment_value_presents (fst y) e'" "additions_value_presents (snd y) a'" "t=Pair_Term e' a'"
    using second unfolding additions_pair_presents_def factor_pair_presents_def by blast
  have same: "e'=e" "a'=a" using left(3) right(3) by simp_all
  have "fst x=fst y" by (rule environment_value_presents_unique[OF left(1) right(1)[unfolded same]])
  moreover have "snd x=snd y" by (rule additions_value_unique[OF left(2) right(2)[unfolded same]])
  ultimately show ?case by (rule prod_eqI)
qed

abbreviation additions_formation_relation where
  "additions_formation_relation x \<equiv>
    environment_additions (fst x) (fst (fst (snd x))) (snd (fst (snd x))) \<and>
    environment_formed (environment_extension (fst x) (fst (fst (snd x))) (snd (fst (snd x)))) \<and>
    octets_formed (snd (snd (snd x)))"

lemma extension_formation_on_pairs:
  assumes presented: "additions_pair_presents x t"
  shows "(954,t)\<in>positive_meaning extension_formation_system \<longleftrightarrow> additions_formation_relation x"
proof -
  obtain e a where e: "environment_value_presents (fst x) e" and a: "additions_value_presents (snd x) a"
    and t: "t=Pair_Term e a"
    using presented unfolding additions_pair_presents_def factor_pair_presents_def by blast
  obtain p where p: "environment_rows_presents (fst (snd x)) p"
    and a': "a=Pair_Term p (site_data_term (fst (snd (snd x))) (snd (snd (snd x))))"
    using a unfolding additions_value_presents_def by blast
  have rows: "environment_rows_presents (fst (fst (snd x)),snd (fst (snd x))) p" using p by simp
  show ?thesis
  proof
    assume "(954,t)\<in>positive_meaning extension_formation_system"
    then obtain E A B q w where parts: "t=Pair_Term (Pair_Term q w) w \<or> True"
      "environment_value_presents E e" "environment_rows_presents (A,B) p"
      "term_formed (site_data_term (fst (snd (snd x))) (snd (snd (snd x))))"
      "environment_additions E A B" "environment_formed (environment_extension E A B)"
      unfolding extension_formation_exact t a' by auto
    have "E=fst x" by (rule environment_value_presents_unique[OF parts(2) e])
    moreover have "A=fst (fst (snd x))" "B=snd (fst (snd x))" using environment_rows_unique[OF parts(3) rows] by (auto simp: prod_eq_iff)
    ultimately show "additions_formation_relation x" using parts(4-6) by simp
  next
    assume relation: "additions_formation_relation x"
    show "(954,t)\<in>positive_meaning extension_formation_system"
      unfolding extension_formation_exact t a'
      by (rule exI[of _ "fst x"], rule exI[of _ e], rule exI[of _ "fst (fst (snd x))"],
        rule exI[of _ "snd (fst (snd x))"], rule exI[of _ p],
        rule exI[of _ "site_data_term (fst (snd (snd x))) (snd (snd (snd x)))"]) (use e p relation in simp)
  qed
qed

theorem extension_formation_equivariant:
  "renaming_equivariant bij (product_action rename_environment additions_renaming) additions_pair_domain
    additions_formation_relation"
proof (unfold renaming_equivariant_def, intro allI impI, goal_cases)
  case (1 h x)
  then have permutation: "bij h" by simp
  obtain E A B s where x: "x=(E,((A,B),s))" by (metis prod.collapse)
  show ?case
    by (simp add: x environment_additions_renaming[OF permutation] environment_extension_renaming[symmetric]
      environment_formed_renaming_iff[OF permutation])
qed

corollary extension_formation_renaming:
  "\<forall>h. bij h \<longrightarrow> rel_fun (renaming_correspondence additions_pair_presents
      (product_action rename_environment additions_renaming) h) (=)
    (\<lambda>p. (954,p)\<in>positive_meaning extension_formation_system) (\<lambda>p. (954,p)\<in>positive_meaning extension_formation_system)"
  using presented_observation_renaming[where observe="\<lambda>p. (954,p)\<in>positive_meaning extension_formation_system"
      and P="\<lambda>x. additions_formation_relation x", OF additions_pair_presentation_class
      renaming_action_product[OF environment_renaming_action additions_renaming_action] extension_formation_on_pairs]
    extension_formation_equivariant by blast

section \<open>The new programs state the empty payload alone\<close>

lemma added_use_fresh_system_payloads [lineage_payloads]: "system_payloads added_use_fresh_system\<subseteq>{[]}"
  unfolding added_use_fresh_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps added_use_fresh_schema_def)

lemma added_uses_fresh_system_payloads [lineage_payloads]: "system_payloads added_uses_fresh_system\<subseteq>{[]}"
  unfolding added_uses_fresh_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

lemma added_binding_system_payloads [lineage_payloads]: "system_payloads added_binding_system\<subseteq>{[]}"
  unfolding added_binding_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps added_binding_clauses_def
    added_binding_added_schema_def added_binding_given_schema_def)

lemma added_bindings_system_payloads [lineage_payloads]: "system_payloads added_bindings_system\<subseteq>{[]}"
  unfolding added_bindings_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps context_list_clauses_def
    context_list_nil_schema_def context_list_step_schema_def)

lemma extension_formation_system_payloads [lineage_payloads]: "system_payloads extension_formation_system\<subseteq>{[]}"
  unfolding extension_formation_system_def
  by ((intro lineage_payload_steps lineage_payloads)?; auto simp: lineage_payload_simps extension_formation_schema_def)

text \<open>
  The additions are the environment value's own rows and the site value's own site: no tag and no new row
  form. G1 reads the given through its admission (26), its artifact table through key absence (20) and its
  uses through the lookup (37), and the added material through the row admission (23 over 22), key
  uniqueness (21) and the binding entry (24) over the added rows alone, so a judgment's calls over the given
  are its entries. Its contract is exact to the extension's formation, and at the given's value and a value
  of the extension it holds exactly where environment inclusion (113) does. The five new definitions state
  the empty payload alone.
\<close>

end
