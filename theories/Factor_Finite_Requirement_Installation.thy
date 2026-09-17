theory Factor_Finite_Requirement_Installation
  imports Factor_Finite_View_Installation Factor_Requirement_Plans Finite_Set_Encoding
begin

section \<open>Finite instructions instantiate the original complete plan constructors\<close>

definition finite_admitted_pair_schema where
  "finite_admitted_pair_schema a b=finite_schema_of (admitted_pair_schema a b)"

lemmas finite_admitted_pair_schema_code [code]=finite_admitted_pair_schema_def
  [unfolded admitted_pair_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma finite_admitted_pair_schema_correct [simp]:
  "decode_finite_schema (finite_admitted_pair_schema a b)=admitted_pair_schema a b"
  by (simp only: finite_admitted_pair_schema_def; rule decode_finite_schema_of) simp

definition finite_data_list_nil_schema where
  "finite_data_list_nil_schema=finite_schema_of data_list_nil_schema"

lemmas finite_data_list_nil_schema_code [code]=finite_data_list_nil_schema_def
  [unfolded data_list_nil_schema_def finite_schema_of_def map_relation_values_def, simplified]

lemma finite_data_list_nil_schema_correct [simp]:
  "decode_finite_schema finite_data_list_nil_schema=data_list_nil_schema"
  by (simp only: finite_data_list_nil_schema_def; rule decode_finite_schema_of)
    (auto simp: data_list_nil_schema_def schema_formed_def single_valued_def octets_formed_def)

lemma admitted_pair_schema_list_step:
  "admitted_pair_schema a b=list_step_schema a b"
  by (simp add: admitted_pair_schema_def list_step_schema_def)

fun finite_admission_instruction_clauses :: "admission_instruction\<Rightarrow>
    nat\<times>(nat\<times>(nat,nat,nat) finite_factor_schema) fset" where
  "finite_admission_instruction_clauses (Pair_Admission_Instruction d a b)=(d,{|(0,finite_admitted_pair_schema a b)|})"
| "finite_admission_instruction_clauses (List_Admission_Instruction d a)=
    (d,{|(0,finite_data_list_nil_schema),(1,finite_admitted_pair_schema a d)|})"

lemma finite_admission_instruction_clauses_correct:
  "(case finite_admission_instruction_clauses i of (d,C) \<Rightarrow>
    (d,map_relation_values decode_finite_schema (fset C)))=admission_instruction_clauses i"
  by (cases i) (simp_all add: map_relation_values_def list_profile_clauses_def admitted_pair_schema_list_step)

fun finite_install_admission_plan :: "(nat,nat,nat,nat) finite_schema_system\<Rightarrow>
    admission_instruction list\<Rightarrow>(nat,nat,nat,nat) finite_schema_system" where
  "finite_install_admission_plan P []=P"
| "finite_install_admission_plan P (i#is)=(case finite_admission_instruction_clauses i of (d,C) \<Rightarrow>
    finite_install_admission_plan (finite_add_view_definition P d (Finite_Variable 0) C) is)"

lemma finite_install_admission_plan_correct [simp]:
  "decode_finite_system (finite_install_admission_plan P cs)=install_admission_plan (decode_finite_system P) cs"
proof (induction cs arbitrary: P)
  case Nil
  then show ?case by simp
next
  case (Cons i cs)
  obtain d C where instruction: "finite_admission_instruction_clauses i=(d,C)" by (cases "finite_admission_instruction_clauses i") auto
  have source: "admission_instruction_clauses i=(d,map_relation_values decode_finite_schema (fset C))"
    using finite_admission_instruction_clauses_correct[of i] by (simp add: instruction)
  show ?case by (simp add: instruction source Cons.IH)
qed

definition finite_requirement_guard_schema :: "('s\<times>'d) fset\<Rightarrow>(nat,'s,'d) finite_factor_schema" where
  "finite_requirement_guard_schema R=\<lparr>finite_schema_conclusion=Finite_Variable 0,
    finite_schema_premises=fimage (\<lambda>(s,d). (s,d,Finite_Variable 0)) R,finite_schema_materials={||}\<rparr>"

lemma finite_requirement_guard_schema_correct [simp]:
  "decode_finite_schema (finite_requirement_guard_schema R)=requirement_guard_schema (fset R)"
  by (simp add: finite_requirement_guard_schema_def requirement_guard_schema_def decode_finite_schema_def
    map_relation_values_def fimage.rep_eq image_image case_prod_unfold decode_finite_call_pattern_def)

definition finite_required_admission_system where
  "finite_required_admission_system P ds k cs=finite_add_view_definition (finite_install_admission_plan P cs) k (Finite_Variable 0)
    {|(0,finite_requirement_guard_schema (fset_of_list (zip [0..<length ds] ds)))|}"

lemma finite_required_admission_system_correct [simp]:
  "decode_finite_system (finite_required_admission_system P ds k cs)=
    required_admission_system (decode_finite_system P) ds k cs"
  by (simp add: finite_required_admission_system_def required_admission_system_def install_requirement_guard_def
    map_relation_values_def fset_of_list.rep_eq requirement_sockets_def)

text \<open>
  Every instruction adds its actual complete clause family to the current
  source, in the original sequence. The final guard retains every requirement
  occurrence, including repetitions and the empty family. These equations
  preserve complete program values; admissibility and meaning use the
  existing checked-plan contracts.
\<close>

end
