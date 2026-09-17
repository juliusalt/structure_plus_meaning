theory Factor_Native_Certificate_Coverage
  imports Factor_Native_Certificate_Cases Finite_Relation_Conflicts
begin

type_synonym native_certificate_coverage_report =
  "native_certificate_paths\<times>
    ((local_address,local_address,local_address) finite_schema_proof\<times>native_certificate_node\<times>native_certificate_node) fset\<times>
    (native_history_call\<times>native_certificate_node\<times>native_certificate_node) fset\<times>
    (native_certificate_node\<times>(local_address list\<times>native_certificate_node)\<times>
      (local_address list\<times>native_certificate_node)) fset"
type_synonym native_certificate_family_coverage_report =
  "(native_certificate_node\<times>native_certificate_coverage_report) fset option"

definition native_certificate_node_coverage where
  "native_certificate_node_coverage P n=(case n of (p,d,t) \<Rightarrow>
    let paths=finite_schema_proof_paths P p d t; nodes=fimage snd paths in
      (paths,finite_projection_conflicts fst nodes,finite_projection_conflicts snd nodes,
        finite_projection_conflicts snd paths))"

definition native_certificate_node_coverage_inspect :: "native_certificate_coverage_report\<Rightarrow>nat\<Rightarrow>bool" where
  "native_certificate_node_coverage_inspect report (f::nat)=(case report of (paths,proofs,calls,shared) \<Rightarrow>
    if f=0 then proofs\<noteq>{||} else if f=1 then calls\<noteq>{||} else if f=2 then shared\<noteq>{||} else False)"

definition native_certificate_node_coverage_condition where
  "native_certificate_node_coverage_condition (f::nat) P n=(case n of (p,d,t) \<Rightarrow>
    if f=0 then (\<exists>a\<in>fset (finite_schema_proof_positions P p d t).
      \<exists>b\<in>fset (finite_schema_proof_positions P p d t). a\<noteq>b \<and> fst a=fst b)
    else if f=1 then (\<exists>a\<in>fset (finite_schema_proof_positions P p d t).
      \<exists>b\<in>fset (finite_schema_proof_positions P p d t). a\<noteq>b \<and> snd a=snd b)
    else if f=2 then (\<exists>ss tt a. ss\<noteq>tt \<and>
      (ss,a) |\<in>| finite_schema_proof_paths P p d t \<and>
      (tt,a) |\<in>| finite_schema_proof_paths P p d t) else False)"

theorem native_certificate_node_coverage_exact:
  "native_certificate_node_coverage_inspect (native_certificate_node_coverage P n) f=
    native_certificate_node_coverage_condition f P n"
proof -
  obtain p d t where shape: "n=(p,d,t)" by (cases n) auto
  have proofs: "finite_projection_conflicts fst (finite_schema_proof_positions P p d t)\<noteq>{||} \<longleftrightarrow>
    (\<exists>a\<in>fset (finite_schema_proof_positions P p d t).
      \<exists>b\<in>fset (finite_schema_proof_positions P p d t). a\<noteq>b \<and> fst a=fst b)"
    by (rule finite_projection_conflicts_nonempty)
  have calls: "finite_projection_conflicts snd (finite_schema_proof_positions P p d t)\<noteq>{||} \<longleftrightarrow>
    (\<exists>a\<in>fset (finite_schema_proof_positions P p d t).
      \<exists>b\<in>fset (finite_schema_proof_positions P p d t). a\<noteq>b \<and> snd a=snd b)"
    by (rule finite_projection_conflicts_nonempty)
  have shared: "finite_projection_conflicts snd (finite_schema_proof_paths P p d t)\<noteq>{||} \<longleftrightarrow>
    (\<exists>ss tt a. ss\<noteq>tt \<and> (ss,a) |\<in>| finite_schema_proof_paths P p d t \<and>
      (tt,a) |\<in>| finite_schema_proof_paths P p d t)"
    by (rule finite_relation_shared_keys)
  show ?thesis
    by (simp only: shape native_certificate_node_coverage_inspect_def native_certificate_node_coverage_def
      native_certificate_node_coverage_condition_def finite_schema_proof_paths_projection
      Let_def case_prod_conv proofs calls shared)
qed

definition native_certificate_family_coverage where
  "native_certificate_family_coverage original=map_option (\<lambda>(P,A,T).
    fimage (\<lambda>n. (n,native_certificate_node_coverage P n)) (native_certificate_nodes T)) original"

definition native_certificate_family_coverage_inspect :: "native_certificate_family_coverage_report\<Rightarrow>nat\<Rightarrow>bool" where
  "native_certificate_family_coverage_inspect report f=(case report of None \<Rightarrow> False
    | Some rows \<Rightarrow> fBex rows (\<lambda>(n,A). native_certificate_node_coverage_inspect A f))"

definition native_certificate_family_coverage_condition where
  "native_certificate_family_coverage_condition f original=(case original of None \<Rightarrow> False
    | Some (P,A,T) \<Rightarrow> (\<exists>n\<in>fset (native_certificate_nodes T).
      native_certificate_node_coverage_condition f P n))"

theorem native_certificate_family_coverage_exact:
  "native_certificate_family_coverage_inspect (native_certificate_family_coverage original) f=
    native_certificate_family_coverage_condition f original"
  by (cases original)
    (auto simp: native_certificate_family_coverage_inspect_def native_certificate_family_coverage_def
      native_certificate_family_coverage_condition_def native_certificate_node_coverage_exact
      fimage.rep_eq split: prod.splits)

definition native_certificate_scope_coverage where
  "native_certificate_scope_coverage originals=map native_certificate_family_coverage originals"

definition native_certificate_scope_coverage_inspect :: "native_certificate_family_coverage_report list\<Rightarrow>nat\<Rightarrow>bool" where
  "native_certificate_scope_coverage_inspect reports f=list_ex
    (\<lambda>A. native_certificate_family_coverage_inspect A f) reports"

definition native_certificate_scope_coverage_condition where
  "native_certificate_scope_coverage_condition f originals=
    (\<exists>original\<in>set originals. native_certificate_family_coverage_condition f original)"

theorem native_certificate_scope_coverage_exact:
  "native_certificate_scope_coverage_inspect (native_certificate_scope_coverage originals) f=
    native_certificate_scope_coverage_condition f originals"
  by (auto simp: native_certificate_scope_coverage_inspect_def native_certificate_scope_coverage_def
    list_ex_iff native_certificate_family_coverage_exact native_certificate_scope_coverage_condition_def)

text \<open>
  The independent conditions require actual original nodes with equal proof
  values and unequal calls, equal calls and unequal proofs, or distinct source
  paths reaching one full node. The original position and path constructors
  already have complete contracts against the independent proof relations.
  Every computed conflict retains both original values and their common key.
  Scope coverage is separate from candidate comparison and graph correctness.
\<close>

end
