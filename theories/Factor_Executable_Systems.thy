theory Factor_Executable_Systems
  imports Factor_Executable_Schemas Factor_Executable_Matching
begin

section \<open>Whole finite programs with complete dependency checks\<close>

record ('a,'s,'d,'c) finite_schema_system =
  finite_system_interfaces :: "('d \<times> 'a finite_term_pattern) fset"
  finite_system_clauses :: "(('d \<times> 'c) \<times> ('a,'s,'d) finite_factor_schema) fset"

definition decode_finite_system ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> ('a,'s,'d,'c) schema_system" where
  "decode_finite_system P =
    \<lparr>system_interfaces=map_relation_values decode_finite_pattern (fset (finite_system_interfaces P)),
     system_clauses=map_relation_values decode_finite_schema (fset (finite_system_clauses P))\<rparr>"

lemma decode_finite_system_fields [simp]:
  "system_interfaces (decode_finite_system P) =
    map_relation_values decode_finite_pattern (fset (finite_system_interfaces P))"
  "system_clauses (decode_finite_system P) =
    map_relation_values decode_finite_schema (fset (finite_system_clauses P))"
  by (simp_all add: decode_finite_system_def)

definition finite_system_definitions :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd fset" where
  "finite_system_definitions P = fimage fst (finite_system_interfaces P)"

lemma finite_system_definitions_correct:
  "fset (finite_system_definitions P) = system_definitions (decode_finite_system P)"
  by (simp add: finite_system_definitions_def system_definitions_def fimage.rep_eq rel_dom_image)

definition finite_system_formed :: "('a,'s,'d,'c) finite_schema_system \<Rightarrow> bool" where
  "finite_system_formed P \<longleftrightarrow>
    finite_relation_functional (finite_system_interfaces P) \<and>
    fBall (finite_system_interfaces P) (\<lambda>(d,p). finite_pattern_formed p) \<and>
    finite_relation_functional (finite_system_clauses P) \<and>
    fBall (finite_system_clauses P) (\<lambda>((d,c),S).
      d |\<in>| finite_system_definitions P \<and> finite_schema_formed S \<and>
      finite_schema_dependencies S |\<subseteq>| finite_system_definitions P)"

lemma finite_system_formed_correct:
  fixes P :: "('a,'s,'d,'c) finite_schema_system"
  shows "finite_system_formed P \<longleftrightarrow> schema_system_formed (decode_finite_system P)"
proof -
  have pi: "inj (decode_finite_pattern :: 'a finite_term_pattern \<Rightarrow> _)"
    and si: "inj (decode_finite_schema :: ('a,'s,'d) finite_factor_schema \<Rightarrow> _)"
    by (auto simp: inj_def)
  show ?thesis
    by (auto simp: finite_system_formed_def schema_system_formed_def
        finite_relation_functional_correct map_relation_values_functional[OF pi]
        map_relation_values_functional[OF si] finite_pattern_formed_correct
        finite_schema_formed_correct finite_schema_dependencies_correct finite_system_definitions_correct
        less_eq_fset.rep_eq Ball_def split_paired_All; blast)
qed

lemma decode_finite_system_injective [simp]:
  fixes P :: "('a,'s,'d,'c) finite_schema_system"
  shows "decode_finite_system P = decode_finite_system Q \<longleftrightarrow> P=Q"
proof -
  have pi: "inj (decode_finite_pattern :: 'a finite_term_pattern \<Rightarrow> _)"
    and si: "inj (decode_finite_schema :: ('a,'s,'d) finite_factor_schema \<Rightarrow> _)"
    by (auto simp: inj_def)
  show ?thesis by (cases P; cases Q)
    (simp add: decode_finite_system_def map_relation_values_injective[OF pi]
      map_relation_values_injective[OF si] fset_inject)
qed

definition finite_system_of ::
  "('a,'s,'d,'c) schema_system \<Rightarrow> ('a,'s,'d,'c) finite_schema_system" where
  "finite_system_of P =
    \<lparr>finite_system_interfaces=Abs_fset (map_relation_values finite_pattern_of (system_interfaces P)),
     finite_system_clauses=Abs_fset (map_relation_values finite_schema_of (system_clauses P))\<rparr>"

lemma decode_finite_system_of:
  assumes formed: "schema_system_formed P"
  shows "decode_finite_system (finite_system_of P) = P"
proof -
  have finite: "finite (system_interfaces P)" "finite (system_clauses P)"
    using formed by (auto simp: schema_system_formed_def)
  have interface: "\<And>d p. (d,p) \<in> system_interfaces P \<Longrightarrow>
      decode_finite_pattern (finite_pattern_of p) = p"
    using formed by (auto simp: schema_system_formed_def intro: decode_finite_pattern_of)
  have clause: "\<And>k S. (k,S) \<in> system_clauses P \<Longrightarrow>
      decode_finite_schema (finite_schema_of S) = S"
    using formed by (auto simp: schema_system_formed_def intro: decode_finite_schema_of)
  have i: "map_relation_values decode_finite_pattern
      (map_relation_values finite_pattern_of (system_interfaces P)) = system_interfaces P"
    by (rule map_relation_values_inverse, rule interface)
  have c: "map_relation_values decode_finite_schema
      (map_relation_values finite_schema_of (system_clauses P)) = system_clauses P"
    by (rule map_relation_values_inverse, rule clause)
  have ifs: "fset (Abs_fset (map_relation_values finite_pattern_of (system_interfaces P))) =
      map_relation_values finite_pattern_of (system_interfaces P)"
    by (rule Abs_fset_inverse) (simp add: finite)
  have cfs: "fset (Abs_fset (map_relation_values finite_schema_of (system_clauses P))) =
      map_relation_values finite_schema_of (system_clauses P)"
    by (rule Abs_fset_inverse) (simp add: finite)
  show ?thesis
    by (rule schema_system.equality)
      (simp_all add: decode_finite_system_def finite_system_of_def ifs cfs i c)
qed

theorem finite_system_representation:
  assumes "schema_system_formed P"
  shows "\<exists>!C. finite_system_formed C \<and> decode_finite_system C=P"
  by (rule ex1I[of _ "finite_system_of P"])
    (use assms decode_finite_system_of[OF assms] in \<open>auto simp: finite_system_formed_correct\<close>)

section \<open>Checking calls and identified inference steps\<close>

definition finite_schema_call_formed ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_schema_call_formed P d t \<longleftrightarrow>
    finite_system_formed P \<and>
    fBex (finite_system_interfaces P) (\<lambda>(e,p). e=d \<and> finite_pattern_accepts p t)"

lemma finite_schema_call_formed_correct:
  "finite_schema_call_formed P d t \<longleftrightarrow>
    schema_call_formed (decode_finite_system P) d (decode_finite_term t)"
  by (auto simp: finite_schema_call_formed_def schema_call_formed_def finite_system_formed_correct
      finite_pattern_accepts_correct Bex_def split_paired_Ex)

definition finite_admitted_schema_instance ::
  "('a,'s,'d,'c) finite_schema_system \<Rightarrow> 'd \<Rightarrow> 'c \<Rightarrow>
    ('a \<times> finite_factor_term) fset \<Rightarrow> finite_factor_term \<Rightarrow>
    ('s \<times> ('d \<times> finite_factor_term)) fset \<Rightarrow> bool" where
  "finite_admitted_schema_instance P d c V t Q \<longleftrightarrow>
    finite_schema_call_formed P d t \<and>
    fBex (finite_system_clauses P) (\<lambda>((e,k),S). e=d \<and> k=c \<and>
      finite_schema_instance S V t Q \<and> finite_schema_material_satisfied S V) \<and>
    fBall Q (\<lambda>(s,e,x). finite_schema_call_formed P e x)"

theorem finite_admitted_schema_instance_correct:
  "finite_admitted_schema_instance P d c V t Q \<longleftrightarrow>
    admitted_schema_instance (decode_finite_system P) d c (decode_finite_term_bindings V)
      (decode_finite_term t) (decode_finite_premises Q)"
  by (auto simp: finite_admitted_schema_instance_def admitted_schema_instance_def
      finite_schema_call_formed_correct finite_schema_instance_correct
      finite_schema_material_satisfied_correct decode_finite_premises_def decode_finite_call_term_def
      Ball_def Bex_def split_paired_All split_paired_Ex; blast)

export_code finite_system_formed finite_schema_call_formed finite_admitted_schema_instance checking SML

text \<open>
  Finite program values retain every interface and identified clause. Formation
  checks the complete dependency boundary; instance checking retains every call
  socket, material socket, and actual binding. The correctness equations apply
  to all finite inputs. These checks decide supplied inference steps. Derivation
  validity still requires checking the links of a complete proof graph.
\<close>

end
