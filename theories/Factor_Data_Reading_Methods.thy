theory Factor_Data_Reading_Methods
  imports Factor_Finite_Quotation_Roots Factor_Finite_Data_Syntax Finite_Relation_Reader_Assessments
begin

type_synonym data_reading_subject = "finite_exact_artifact\<times>local_address"

definition data_reading_method :: "nat \<Rightarrow> data_reading_subject \<Rightarrow> finite_factor_term fset" where
  "data_reading_method m X=(case X of (C,r) \<Rightarrow>
    if m=0 then finite_complete_data_readings C r
    else if m=1 then finite_complete_data_readings_prepared C r
    else if m=2 then finite_complete_data_body_values C r
    else if m=3 then (if r=[] then finite_complete_data_readings_prepared C r else {||})
    else if m=6 then finite_complete_data_readings_at_roots C r
    else if m=5 then finite_complete_data_readings_prepared
      (C\<lparr>finite_data:=(finite_data C)\<lparr>finite_bag:={#}\<rparr>\<rparr>) r
    else {||})"

definition data_reading_condition where
  "data_reading_condition (f::nat) method X=(case X of (C,r) \<Rightarrow>
    if f=0 then (\<forall>t. t |\<in>| method X \<longrightarrow>
      complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t))
    else if f=1 then (\<forall>t. complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t)
      \<longrightarrow> t |\<in>| method X) else False)"

lemma data_reading_original_condition:
  "f\<in>{0,1} \<Longrightarrow> data_reading_condition f (data_reading_method 0) X"
  by (cases X) (auto simp: data_reading_condition_def data_reading_method_def finite_complete_data_readings_exact)

lemma data_reading_prepared_condition:
  "f\<in>{0,1} \<Longrightarrow> data_reading_condition f (data_reading_method 1) X"
  by (cases X) (auto simp: data_reading_condition_def data_reading_method_def
    finite_complete_data_readings_prepared_exact finite_complete_data_readings_exact)

lemma data_reading_root_condition:
  "f\<in>{0,1} \<Longrightarrow> data_reading_condition f (data_reading_method 6) X"
  by (cases X) (auto simp: data_reading_condition_def data_reading_method_def
    finite_complete_data_readings_at_roots_exact finite_complete_data_readings_exact)

definition data_reading_case :: "finite_exact_artifact \<Rightarrow> nat \<Rightarrow> data_reading_subject" where
  "data_reading_case C w=(let P=finite_payload_syntax [7];
    Q=finite_pair_syntax (finite_payload_syntax [1]) (finite_payload_syntax [2]) in
    if w=0 then (P,[]) else if w=1 then (Q,[])
    else if w=2 then (finite_payload_syntax [256],[]) else if w=3 then (P,[9])
    else if w=4 then (finite_syntax_union Q finite_empty_artifact,[2])
    else if w=5 then (finite_attach_structure Q \<lparr>finite_carrier={|[99]|},finite_incidence={||}\<rparr>,[])
    else if w=6 then (C,[]) else if w=7 then (finite_syntax_union C finite_empty_artifact,[2])
    else if w=8 then (finite_empty_artifact,[]) else if w=9 then (finite_payload_syntax [],[])
    else if w=10 then (finite_enumerated_artifact [[]] [] [([],[]),([],[])] [([],[7])],[])
    else (finite_enumerated_artifact [[]] [] [] [],[]))"

definition data_reading_context where
  "data_reading_context X=(case X of (C,r) \<Rightarrow> (X,finite_complete_data_readings C r))"

definition data_reading_assessment where
  "data_reading_assessment m context=(case context of (X,reference) \<Rightarrow> (if m=0 then (reference,reference) else (data_reading_method m X,reference)))"

definition data_reading_inspect :: "(finite_factor_term fset\<times>finite_factor_term fset)\<Rightarrow>nat\<Rightarrow>bool" where
  "data_reading_inspect=finite_reader_inspect"

theorem data_reading_assessment_exact:
  "data_reading_inspect (data_reading_assessment m (data_reading_context X)) f=
    data_reading_condition f (data_reading_method m) X"
proof -
  obtain C r where fields: "X=(C,r)" by (cases X) auto
  have reference: "t |\<in>| finite_complete_data_readings C r \<longleftrightarrow>
    complete_data_quoted_at (decode_finite_object C) r (decode_finite_term t)" for t
    by (rule finite_complete_data_readings_exact)
  have report: "data_reading_assessment m (data_reading_context (C,r))=
    (data_reading_method m (C,r),finite_complete_data_readings C r)"
    by (cases "m=0") (simp_all add: data_reading_assessment_def data_reading_context_def data_reading_method_def)
  show ?thesis
    by (simp only: fields report data_reading_inspect_def finite_reader_inspect_exact[OF reference]
      data_reading_condition_def relation_reader_condition_def case_prod_conv)
qed

text \<open>
  The reference operation derives complete quotation readings from the actual
  source. Soundness and completeness refer independently to complete_data_quoted_at.
  Native controls omit formation, require the canonical root, return no reading,
  or erase counted attachments. The supplied complete artifact remains an
  ordinary structural operand, and no expected satisfaction flags are accepted.
\<close>

end
