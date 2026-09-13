theory Factor_Admission_Plans
  imports Factor_Admitted_Pair Factor_List_Set_Presentations
begin

section \<open>Admission requirements retain their component predicates\<close>

datatype admission_goal =
    Existing_Admission nat
  | Paired_Admission admission_goal admission_goal
  | Collected_Admission admission_goal

fun admission_goal_sites :: "admission_goal \<Rightarrow> nat set" where
  "admission_goal_sites (Existing_Admission d)={d}"
| "admission_goal_sites (Paired_Admission g h)=admission_goal_sites g\<union>admission_goal_sites h"
| "admission_goal_sites (Collected_Admission g)=admission_goal_sites g"

fun admission_goal_holds :: "(nat\<times>factor_term) set \<Rightarrow> admission_goal \<Rightarrow> factor_term \<Rightarrow> bool" where
  "admission_goal_holds M (Existing_Admission d) t \<longleftrightarrow> (d,t)\<in>M"
| "admission_goal_holds M (Paired_Admission g h) t \<longleftrightarrow>
    (\<exists>x y. t=Pair_Term x y \<and> admission_goal_holds M g x \<and> admission_goal_holds M h y)"
| "admission_goal_holds M (Collected_Admission g) t \<longleftrightarrow>
    (\<exists>xs. t=data_list_term xs \<and> (\<forall>x\<in>set xs. admission_goal_holds M g x))"

lemma admission_goal_holds_agreement:
  assumes "\<And>d t. d\<in>admission_goal_sites g \<Longrightarrow> ((d,t)\<in>M \<longleftrightarrow> (d,t)\<in>N)"
  shows "admission_goal_holds M g t \<longleftrightarrow> admission_goal_holds N g t"
  using assms by (induction g arbitrary: t) auto

lemma admission_paired_holds:
  "admission_goal_holds M (Paired_Admission g h) (Pair_Term x y) \<longleftrightarrow>
    admission_goal_holds M g x \<and> admission_goal_holds M h y"
  by simp

lemma admission_collected_empty [simp]:
  "admission_goal_holds M (Collected_Admission g) (Payload_Term [])"
  by (simp only: admission_goal_holds.simps; rule exI[of _ "[]"]) simp

lemma admission_collected_pair:
  "admission_goal_holds M (Collected_Admission g) (Pair_Term x y) \<longleftrightarrow>
    admission_goal_holds M g x \<and> admission_goal_holds M (Collected_Admission g) y"
proof
  assume "admission_goal_holds M (Collected_Admission g) (Pair_Term x y)"
  then obtain xs where shape: "Pair_Term x y=data_list_term xs"
    and elements: "\<forall>z\<in>set xs. admission_goal_holds M g z" by auto
  obtain z zs where list: "xs=z#zs" using shape by (cases xs) auto
  have fields: "x=z" "y=data_list_term zs" using shape list by simp_all
  show "admission_goal_holds M g x \<and> admission_goal_holds M (Collected_Admission g) y"
    using elements list fields by auto
next
  assume "admission_goal_holds M g x \<and> admission_goal_holds M (Collected_Admission g) y"
  then obtain xs where first: "admission_goal_holds M g x" and tail: "y=data_list_term xs"
    "\<forall>z\<in>set xs. admission_goal_holds M g z" by auto
  show "admission_goal_holds M (Collected_Admission g) (Pair_Term x y)"
    by (simp only: admission_goal_holds.simps; rule exI[of _ "x#xs"])
      (use first tail in simp)
qed

section \<open>The plan contains actual constructor arguments\<close>

datatype admission_instruction = Pair_Admission_Instruction nat nat nat | List_Admission_Instruction nat nat

fun admission_instruction_clauses :: "admission_instruction \<Rightarrow> nat\<times>(nat\<times>(nat,nat,nat) factor_schema) set" where
  "admission_instruction_clauses (Pair_Admission_Instruction d a b)=(d,{(0,admitted_pair_schema a b)})"
| "admission_instruction_clauses (List_Admission_Instruction d a)=(d,list_profile_clauses a d)"

fun install_admission_plan :: "(nat,nat,nat,nat) schema_system \<Rightarrow> admission_instruction list \<Rightarrow>
    (nat,nat,nat,nat) schema_system" where
  "install_admission_plan P []=P"
| "install_admission_plan P (i#is)=
    (case admission_instruction_clauses i of (d,C) \<Rightarrow>
      install_admission_plan (add_view_definition P d data_x C) is)"

fun admission_plan :: "admission_goal \<Rightarrow> nat \<Rightarrow> nat\<times>(nat\<times>admission_instruction list)" where
  "admission_plan (Existing_Admission d) n=(d,n,[])"
| "admission_plan (Paired_Admission g h) n=
    (case admission_plan g n of (a,m,is) \<Rightarrow>
      case admission_plan h m of (b,k,js) \<Rightarrow>
        (k,Suc k,is@js@[Pair_Admission_Instruction k a b]))"
| "admission_plan (Collected_Admission g) n=
    (case admission_plan g n of (a,m,is) \<Rightarrow> (m,Suc m,is@[List_Admission_Instruction m a]))"

lemma install_admission_plan_append:
  "install_admission_plan P (is@js)=install_admission_plan (install_admission_plan P is) js"
  by (induction "is" arbitrary: P) (auto split: prod.splits)

section \<open>Finite values expose every goal and instruction field\<close>

abbreviation admission_counter :: "nat \<Rightarrow> factor_term" where
  "admission_counter n \<equiv> data_list_term (replicate n (Payload_Term []))"

lemma admission_counter_injective [simp]: "admission_counter m=admission_counter n \<longleftrightarrow> m=n"
  by (simp add: data_list_term_injective)

lemma admission_counter_formed [simp]: "term_formed (admission_counter n)"
  by (simp add: data_list_term_formed octets_formed_def)

lemma admission_counter_self_contained [simp]: "self_contained_term (admission_counter n)"
  by (simp add: data_list_term_self_contained)

fun admission_goal_value :: "admission_goal \<Rightarrow> factor_term" where
  "admission_goal_value (Existing_Admission d)=Pair_Term (Payload_Term [0]) (admission_counter d)"
| "admission_goal_value (Paired_Admission g h)=
    Pair_Term (Payload_Term [1]) (Pair_Term (admission_goal_value g) (admission_goal_value h))"
| "admission_goal_value (Collected_Admission g)=Pair_Term (Payload_Term [2]) (admission_goal_value g)"

fun admission_instruction_value :: "admission_instruction \<Rightarrow> factor_term" where
  "admission_instruction_value (Pair_Admission_Instruction d a b)=
    data_list_term [admission_counter d,admission_counter a,admission_counter b]"
| "admission_instruction_value (List_Admission_Instruction d a)=
    data_list_term [admission_counter d,admission_counter a]"

lemma admission_goal_value_injective [simp]: "admission_goal_value g=admission_goal_value h \<longleftrightarrow> g=h"
  by (induction g arbitrary: h) (case_tac h; auto)+

lemma admission_goal_value_formed [simp]: "term_formed (admission_goal_value g)"
  by (induction g) (auto simp: octets_formed_def)

lemma admission_instruction_value_injective [simp]:
  "admission_instruction_value i=admission_instruction_value j \<longleftrightarrow> i=j"
  by (cases i; cases j) auto

lemma admission_instruction_value_formed [simp]: "term_formed (admission_instruction_value i)"
  by (cases i) (auto simp: octets_formed_def)

lemma admission_instruction_value_self_contained [simp]: "self_contained_term (admission_instruction_value i)"
  by (cases i) auto

lemma admission_instruction_list_data [simp]:
  "data_elements (map admission_instruction_value xs)"
  by auto

text \<open>
  A goal names existing predicate sites in one supplied program and combines
  their admission requirements. Applying a goal to an independently defined
  subject still requires its exact local presentation contract. The goal does
  not redefine that subject. Pairing retains both fields; collection admission
  visits every element and admits the empty collection.

  The plan records each fresh entry and every actual callee. Installation uses
  the existing pair and list schemas. The supplied initial counter must be
  outside the source program, and every named component must exist there;
  producing a plan alone does not discharge these conditions.

  The datatypes project the displayed finite fields. Goal tags distinguish
  presentation forms. Their operative use must be supplied by the native
  planning clauses and its exactness theorem. These declarations alone are
  not native execution or native mathematical-proof admission.
\<close>

end
