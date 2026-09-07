theory Factor_Proof_Metadata
  imports Factor_Table_Metadata Factor_Derivation_Graphs
begin

section \<open>Inference metadata and an explicit empty assertion form\<close>

inductive native_proof_node_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    ('u definition_site,'u definition_site) schema_graph_node \<Rightarrow>
    ('u definition_site \<times> 'u definition_site) set \<Rightarrow>
    local_address set \<Rightarrow> local_address set \<Rightarrow> bool"
  for E u r where
  assertion:
    "environment_formed E \<Longrightarrow> artifact_at E u R \<Longrightarrow> record_at R r [] [] \<Longrightarrow>
     native_proof_node_at E u r Schema_Assertion {} {r} {}"
| inference:
    "environment_formed E \<Longrightarrow> artifact_at E u R \<Longrightarrow> record_at R r ps [c,b,p] \<Longrightarrow>
     site_citation_at E u c d C A \<Longrightarrow>
     native_binding_table_at E u b (fset V) B L \<Longrightarrow>
     native_discharge_table_at E u p D J W \<Longrightarrow>
     insert r (set ps) \<inter> (C \<union> B \<union> J) = {} \<Longrightarrow>
     C \<inter> B = {} \<Longrightarrow> C \<inter> J = {} \<Longrightarrow> B \<inter> J = {} \<Longrightarrow>
     insert r (set ps \<union> C \<union> B \<union> J) \<inter> (A \<union> L \<union> W) = {} \<Longrightarrow>
     native_proof_node_at E u r (Schema_Inference d V) D
       (insert r (set ps \<union> C \<union> B \<union> J)) (A \<union> L \<union> W)"

lemma native_proof_node_assertion:
  assumes node: "native_proof_node_at E u r Schema_Assertion D I K"
  shows "D={} \<and> I={r} \<and> K={}"
  using node by (cases rule: native_proof_node_at.cases) auto

lemma native_proof_node_unique:
  assumes first: "native_proof_node_at E u r N D I K"
    and second: "native_proof_node_at E u r M F J A"
  shows "N=M \<and> D=F \<and> I=J \<and> K=A"
proof (cases rule: native_proof_node_at.cases[OF first, case_names assertion inference])
  case (assertion R)
  have ef: "environment_formed E" and source: "artifact_at E u R" and frame: "record_at R r [] []"
    using assertion by auto
  have art: "\<And>S. artifact_at E u S \<Longrightarrow> S=R"
    by (rule environment_artifact_unique[OF ef _ source])
  have rec: "\<And>ps xs. record_at R r ps xs \<Longrightarrow> ps=[] \<and> xs=[]"
    using record_at_unique[OF _ frame] by blast
  show ?thesis using assertion
    by (cases rule: native_proof_node_at.cases[OF second]) (auto dest!: art rec)
next
  case (inference R ps c b p d C U V B L D' X W)
  have ef: "environment_formed E" and source: "artifact_at E u R"
    and frame: "record_at R r ps [c,b,p]" and reference: "site_citation_at E u c d C U"
    and bindings: "native_binding_table_at E u b (fset V) B L"
    and discharges: "native_discharge_table_at E u p D' X W"
    using inference by auto
  have art: "\<And>S. artifact_at E u S \<Longrightarrow> S=R"
    by (rule environment_artifact_unique[OF ef _ source])
  have rec: "\<And>qs xs. record_at R r qs xs \<Longrightarrow> qs=ps \<and> xs=[c,b,p]"
    using record_at_unique[OF _ frame] by blast
  have cite: "\<And>e Y Z. site_citation_at E u c e Y Z \<Longrightarrow> e=d \<and> Y=C \<and> Z=U"
    using site_citation_unique[OF _ reference] by blast
  have binding: "\<And>V' Y Z. native_binding_table_at E u b (fset V') Y Z \<Longrightarrow> V'=V \<and> Y=B \<and> Z=L"
    using native_table_unique[OF _ bindings] by auto
  have premise: "\<And>F Y Z. native_discharge_table_at E u p F Y Z \<Longrightarrow> F=D' \<and> Y=X \<and> Z=W"
    using native_table_unique[OF _ discharges] by blast
  show ?thesis using inference
    by (cases rule: native_proof_node_at.cases[OF second]) (auto dest!: art rec cite binding premise)
qed

lemma native_proof_node_properties:
  assumes node: "native_proof_node_at E u r N D I K"
  shows "environment_formed E" "(u,r) \<in> environment_positions E"
    "finite D" "single_valued D" "r \<in> I" "finite I" "finite K" "I \<inter> K = {}"
    "\<forall>s n. (s,n) \<in> D \<longrightarrow> s \<in> environment_positions E \<and> n \<in> environment_positions E"
proof -
  have properties: "environment_formed E \<and> (u,r) \<in> environment_positions E \<and>
    finite D \<and> single_valued D \<and> r \<in> I \<and> finite I \<and> finite K \<and> I \<inter> K = {} \<and>
    (\<forall>s n. (s,n) \<in> D \<longrightarrow> s \<in> environment_positions E \<and> n \<in> environment_positions E)"
  proof (cases rule: native_proof_node_at.cases[OF node, case_names assertion inference])
    case (assertion R)
    then show ?thesis by (auto simp: record_at_def single_valued_def)
  next
    case (inference R ps c b p d C A V B L D' J W)
    have reference: "site_citation_at E u c d C A"
      and bindings: "native_binding_table_at E u b (fset V) B L"
      and discharges: "native_discharge_table_at E u p D' J W"
      using inference by auto
    have cf: "finite C" "finite A" using site_citation_properties(2,3)[OF reference] by blast+
    have bf: "finite B" "finite L" using native_binding_table_properties(4,5)[OF bindings] by blast+
    have df: "finite D'" "single_valued D'" "finite J" "finite W"
      using native_discharge_table_properties(1,2,4,5)[OF discharges] by blast+
    have targets: "\<forall>s n. (s,n) \<in> D' \<longrightarrow> s \<in> environment_positions E \<and> n \<in> environment_positions E"
      by (rule native_discharge_table_properties(7)[OF discharges])
    have position: "(u,r) \<in> environment_positions E" using inference by (auto simp: record_at_def)
    show ?thesis using inference cf bf df targets position by auto
  qed
  show "environment_formed E" "(u,r) \<in> environment_positions E"
    "finite D" "single_valued D" "r \<in> I" "finite I" "finite K" "I \<inter> K = {}"
    "\<forall>s n. (s,n) \<in> D \<longrightarrow> s \<in> environment_positions E \<and> n \<in> environment_positions E"
    using properties by blast+
qed

lemma native_proof_node_carrier:
  assumes node: "native_proof_node_at E u r N D I K" and art: "artifact_at E u R"
  shows "I \<union> K \<subseteq> rra_carrier (object_structure R)"
proof (cases rule: native_proof_node_at.cases[OF node, case_names assertion inference])
  case (assertion S)
  have ef: "environment_formed E" and source: "artifact_at E u S" and frame: "record_at S r [] []"
    using assertion by auto
  have same: "S=R" by (rule environment_artifact_unique[OF ef source art])
  show ?thesis using record_interior_in_carrier[OF frame] assertion same by simp
next
  case (inference S ps c b p d C A V B L D' J W)
  have ef: "environment_formed E" and source: "artifact_at E u S"
    and frame: "record_at S r ps [c,b,p]" and reference: "site_citation_at E u c d C A"
    and bindings: "native_binding_table_at E u b (fset V) B L"
    and discharges: "native_discharge_table_at E u p D' J W"
    using inference by auto
  have same: "S=R" by (rule environment_artifact_unique[OF ef source art])
  show ?thesis using record_interior_in_carrier[OF frame] site_citation_carrier[OF reference art]
    native_binding_table_carrier[OF bindings art] native_discharge_table_carrier[OF discharges art]
    inference same by blast
qed

text \<open>
  An inference is a three-field record containing its clause citation, complete
  binding table, and complete premise-discharge table. An assertion is an
  explicit empty record. No node stores its conclusion or an assumption list.
  These readers recover finite syntax without validating any derivation.
\<close>

end
