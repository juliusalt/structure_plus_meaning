theory Factor_Finite_Data_Syntax
  imports Factor_Finite_Artifact_Enumeration Factor_Executable_Data_Values Factor_Complete_Data_Quotation
begin

section \<open>Finite constructors preserve the complete existing data syntax\<close>

definition finite_payload_syntax :: "octets \<Rightarrow> finite_exact_artifact" where
  "finite_payload_syntax v=finite_enumerated_artifact [[]] [] [] [([],v)]"

lemma decode_finite_payload_syntax [simp]:
  "decode_finite_object (finite_payload_syntax v)=payload_syntax v"
  by (simp add: finite_payload_syntax_def enumerated_artifact_def payload_syntax_def fun_eq_iff)

definition finite_pair_syntax :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_pair_syntax R S=\<lparr>
    finite_structure=\<lparr>
      finite_carrier={|[],[0],[1]|} |\<union>|
        fimage (Cons 2) (finite_carrier (finite_structure R)) |\<union>|
        fimage (Cons 3) (finite_carrier (finite_structure S)),
      finite_incidence={|([],[0],[2]),([],[1],[3]),([0],[0],[1])|} |\<union>|
        fimage (\<lambda>(a,p,x). (2#a,2#p,2#x)) (finite_incidence (finite_structure R)) |\<union>|
        fimage (\<lambda>(a,p,x). (3#a,3#p,3#x)) (finite_incidence (finite_structure S))\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings=
      fimage (\<lambda>(a,v). (2#a,v)) (finite_bindings (finite_data R)) |\<union>|
      fimage (\<lambda>(a,v). (3#a,v)) (finite_bindings (finite_data S))\<rparr>\<rparr>"

lemma decode_finite_pair_syntax [simp]:
  "decode_finite_object (finite_pair_syntax R S)=pair_syntax (decode_finite_object R) (decode_finite_object S)"
  by (simp add: finite_pair_syntax_def pair_syntax_def decode_finite_object_def
    decode_finite_structure_def decode_finite_basis_def push_structure_def
    fimage.rep_eq fun_eq_iff)

fun finite_data_syntax :: "factor_term \<Rightarrow> finite_exact_artifact option" where
  "finite_data_syntax (Target_Term t)=None"
| "finite_data_syntax (Payload_Term v)=Some (finite_payload_syntax v)"
| "finite_data_syntax (Pair_Term x y)=
    (case finite_data_syntax x of None \<Rightarrow> None
      | Some R \<Rightarrow> map_option (finite_pair_syntax R) (finite_data_syntax y))"

lemma finite_data_syntax_domain:
  "finite_data_syntax t=None \<longleftrightarrow> \<not>self_contained_term t"
  by (induction t) (auto split: option.splits)

lemma finite_data_syntax_sound:
  assumes "finite_data_syntax t=Some C"
  shows "decode_finite_object C=term_syntax t"
  using assms by (induction t arbitrary: C) (auto split: option.splits)

theorem finite_data_syntax_exact:
  "finite_data_syntax t=Some C \<longleftrightarrow>
    self_contained_term t \<and> decode_finite_object C=term_syntax t"
proof
  assume built: "finite_data_syntax t=Some C"
  then show "self_contained_term t \<and> decode_finite_object C=term_syntax t"
    using finite_data_syntax_domain[of t] finite_data_syntax_sound[OF built] by auto
next
  assume parts: "self_contained_term t \<and> decode_finite_object C=term_syntax t"
  obtain B where built: "finite_data_syntax t=Some B"
    using parts finite_data_syntax_domain[of t] by (cases "finite_data_syntax t") auto
  have right: "decode_finite_object C=term_syntax t" using parts by blast
  have decoded: "decode_finite_object B=decode_finite_object C"
    by (rule trans[OF finite_data_syntax_sound[OF built] right[symmetric]])
  have same: "B=C" using decoded by (simp only: decode_finite_object_injective)
  show "finite_data_syntax t=Some C" using built same by simp
qed

theorem finite_data_syntax_complete_quotation:
  assumes formed: "term_formed t" and built: "finite_data_syntax t=Some C"
  shows "complete_data_quoted_at (decode_finite_object C) [] t"
proof -
  have closed: "self_contained_term t" and decode: "decode_finite_object C=term_syntax t"
    using built by (simp_all add: finite_data_syntax_exact)
  show ?thesis by (simp only: decode; rule complete_data_quotation_total[OF formed closed])
qed

export_code finite_data_syntax checking SML

text \<open>
  The constructors use the existing payload and pair syntax and preserve its
  complete incidence and bindings. Their decoding equation is exact object
  equality. They reject target-bearing terms and preserve malformed payload
  bytes for the separate formation and admission checks.
\<close>

end
