theory Factor_Required_Cause_Assessment
  imports Factor_Required_Cause_Cases Boolean_Decision_Assessments
begin

definition required_cause_alignment_report where
  "required_cause_alignment_report K pu d R q=(case q of (F,qu,qr,au,ar) \<Rightarrow>
    (q,qu=pu \<and> qr=[],finite_native_package_environment F qu qr=finite_native_package_environment K pu [],
      finite_application_readings F au ar,finite_application_value_ready F au ar d (Finite_Target (Finite_Whole R))))"

definition required_cause_report where
  "required_cause_report X=(case X of ((S,su,sr,gs),(E,gu,gr,G,H,root,R)) \<Rightarrow>
    let scopes=finite_generation_judgment_readings E gu gr G;
      original=finite_construct_source_requirements S su sr gs
    in (finite_certified_base_cause E gu gr G H root R,scopes,map_option (\<lambda>(d,K,pu).
      ((d,K,pu),finite_native_package_readings K pu [],
        fimage (required_cause_alignment_report K pu d R) scopes)) original,
      finite_requirement_decision S su sr gs {|Finite_Target (Finite_Whole R)|}))"

definition required_cause_row_decide where
  "required_cause_row_decide (m::nat) row=(case row of (q,site,scope,apps,entry) \<Rightarrow>
    site \<and> (m=3 \<or> scope) \<and> (m=2 \<or> entry))"

definition required_cause_decide where
  "required_cause_decide (m::nat) report=(case report of (certified,scopes,policy,decision) \<Rightarrow>
    if m=1 then certified else if m=5 then False else if m=6 then True
    else case policy of None \<Rightarrow> (m=7 \<and> certified)
      | Some (source,programs,rows) \<Rightarrow> programs\<noteq>{||} \<and> (m=4 \<or> certified) \<and>
        fBex rows (required_cause_row_decide m))"

lemma required_cause_row_original:
  "required_cause_row_decide 0 (required_cause_alignment_report K pu d R q)=
    finite_policy_cause_alignment K pu [] d R q"
  by (cases q) (simp add: required_cause_row_decide_def required_cause_alignment_report_def
    finite_policy_cause_alignment_def split: prod.splits)

lemma required_cause_report_original:
  "required_cause_decide 0 (required_cause_report X)=required_cause_direct X"
proof -
  have each: "fBex (fimage (required_cause_alignment_report K pu d R) scopes)
      (required_cause_row_decide 0)=fBex scopes (finite_policy_cause_alignment K pu [] d R)" for K pu d R scopes
    by (simp only: FSet.bex_simps(5) required_cause_row_original)
  show ?thesis by (cases X) (simp add: required_cause_decide_def required_cause_report_def
    required_cause_direct_def finite_required_cause_def finite_certified_policy_cause_def Let_def each
    required_cause_row_original
    split: prod.splits option.splits)
qed

definition required_cause_method where
  "required_cause_method m X=required_cause_decide m (required_cause_report X)"

lemma required_cause_method_original:
  "required_cause_method 0=required_cause_holds"
  by (rule ext) (simp only: required_cause_method_def required_cause_report_original required_cause_direct_exact)

definition required_cause_family_condition where
  "required_cause_family_condition f method subjects=decision_family_condition f required_cause_holds
    method (required_cause_covered,subjects)"

definition required_cause_family_assessment where
  "required_cause_family_assessment m subjects=decision_family_assessment
    required_cause_report (required_cause_decide 0) (required_cause_decide m) (required_cause_covered,subjects)"

lemma required_cause_method_composition:
  "required_cause_decide m \<circ> required_cause_report=required_cause_method m"
  by (rule ext) (simp only: comp_apply required_cause_method_def)

lemma required_cause_family_assessment_exact:
  "decision_family_inspect (required_cause_family_assessment m subjects) f=
    required_cause_family_condition f (required_cause_method m) subjects"
  by (simp only: required_cause_family_assessment_def decision_family_assessment_exact
    required_cause_family_condition_def required_cause_method_composition required_cause_method_original)

end
