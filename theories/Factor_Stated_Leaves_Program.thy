theory Factor_Stated_Leaves_Program
  imports Factor_Stated_Leaves Native_Control_Quotation_Code
begin

section \<open>The stated-leaves reader's program presented finitely\<close>

text \<open>
  The reader's program (@{const stated_report_system}, entry 590) is presented once, by the finite presentation of
  the program itself. Its code equation is derived part by part: the reader's eleven views (580 to 590) and the
  payload audit's six (500 to 505) are each a view extension of what precedes it, presented by the finite view
  extension of its predecessor's presentation, and definition admission, where the audit's lineage begins, is the
  piece @{const finite_call_admission_program}, reduced nowhere again.
\<close>

definition finite_stated_report_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "finite_stated_report_program=finite_system_of stated_report_system"

lemma finite_stated_report_program_exact:
  "decode_finite_system finite_stated_report_program=stated_report_system"
  unfolding finite_stated_report_program_def
  by (rule decode_finite_system_of[OF stated_report_system_formed])

lemma finite_stated_report_program_formed:
  "finite_system_formed finite_stated_report_program"
  by (simp only: finite_system_formed_correct finite_stated_report_program_exact stated_report_system_formed)

local_setup \<open>Native_Finite_Equations.note_composed @{binding finite_stated_report_program_code}
  @{thm finite_stated_report_program_def} [@{thm finite_call_admission_program_def}] []\<close>

section \<open>The reader's contract at its presentation\<close>

text \<open>
  The reader's exact contract (@{thm [source] stated_report_exact}) at the program its presentation decodes to.
\<close>

theorem finite_stated_report_exact:
  "(590,z)\<in>positive_meaning (decode_finite_system finite_stated_report_program) \<longleftrightarrow> stated_report_result z"
  by (simp only: finite_stated_report_program_exact stated_report_exact)

end
