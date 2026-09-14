theory RRA_Finite_Syntax_Construction
  imports RRA_Executable_Syntax RRA_Bound_Forests RRA_Syntax_Forests RRA_External_Occurrence_Syntax
begin

section \<open>Finite construction preserves the existing complete syntax objects\<close>

definition finite_payload_syntax :: "octets \<Rightarrow> finite_exact_artifact" where
  "finite_payload_syntax v=\<lparr>finite_structure=\<lparr>finite_carrier={|[]|},finite_incidence={||}\<rparr>,
    finite_data=finite_payload_basis [] v\<rparr>"

lemma decode_finite_payload_syntax [simp]:
  "decode_finite_object (finite_payload_syntax v)=payload_syntax v"
  by (simp add: finite_payload_syntax_def payload_syntax_def decode_finite_object_def decode_finite_structure_def)

definition finite_external_occurrence_syntax :: "local_address\<Rightarrow>finite_exact_artifact" where
  "finite_external_occurrence_syntax a=\<lparr>
    finite_structure=\<lparr>finite_carrier={|[],[4],[5]|},finite_incidence={|([],[],[4]),([],[4],[5])|}\<rparr>,
    finite_data=finite_payload_basis [5] a\<rparr>"

lemma decode_finite_external_occurrence_syntax [simp]:
  "decode_finite_object (finite_external_occurrence_syntax a)=external_occurrence_syntax a"
  by (simp add: finite_external_occurrence_syntax_def external_occurrence_syntax_def
    decode_finite_object_def decode_finite_structure_def)

fun finite_literal_syntax :: "finite_exact_target \<Rightarrow> finite_exact_artifact" where
  "finite_literal_syntax (Finite_Whole R)=\<lparr>
    finite_structure=\<lparr>finite_carrier={|[],[4]|},finite_incidence={|([],[4],[4])|}\<rparr>,
    finite_data=finite_empty_basis\<rparr>"
| "finite_literal_syntax (Finite_Anchor R a)=finite_external_occurrence_syntax a"

lemma decode_finite_literal_syntax [simp]:
  "decode_finite_object (finite_literal_syntax t)=literal_syntax (decode_finite_target t)"
  by (cases t) (simp_all add: finite_external_occurrence_syntax_def decode_finite_object_def decode_finite_structure_def)

definition finite_syntax_join ::
  "(local_address\<Rightarrow>local_address) \<Rightarrow> (local_address\<Rightarrow>local_address) \<Rightarrow>
    local_address fset \<Rightarrow> (local_address\<times>local_address\<times>local_address) fset \<Rightarrow>
    finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_syntax_join f g U I R S=\<lparr>finite_structure=\<lparr>
    finite_carrier=U |\<union>| fimage f (finite_carrier (finite_structure R)) |\<union>|
      fimage g (finite_carrier (finite_structure S)),
    finite_incidence=I |\<union>| fimage (\<lambda>(a,p,x). (f a,f p,f x)) (finite_incidence (finite_structure R)) |\<union>|
      fimage (\<lambda>(a,p,x). (g a,g p,g x)) (finite_incidence (finite_structure S))\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings=
      fimage (\<lambda>(a,v). (f a,v)) (finite_bindings (finite_data R)) |\<union>|
      fimage (\<lambda>(a,v). (g a,v)) (finite_bindings (finite_data S))\<rparr>\<rparr>"

lemma decode_finite_syntax_join:
  "decode_finite_object (finite_syntax_join f g U I R S)=\<lparr>object_structure=\<lparr>
    rra_carrier=fset U \<union> f ` rra_carrier (object_structure (decode_finite_object R)) \<union>
      g ` rra_carrier (object_structure (decode_finite_object S)),
    rra_incidence=fset I \<union> rra_incidence (push_structure f (object_structure (decode_finite_object R))) \<union>
      rra_incidence (push_structure g (object_structure (decode_finite_object S)))\<rparr>,
    object_data=\<lparr>bag_count=(\<lambda>_. 0),functional_bindings=
      (\<lambda>(a,v). (f a,v)) ` functional_bindings (object_data (decode_finite_object R)) \<union>
      (\<lambda>(a,v). (g a,v)) ` functional_bindings (object_data (decode_finite_object S))\<rparr>\<rparr>"
  by (simp add: finite_syntax_join_def decode_finite_object_def decode_finite_structure_def
    decode_finite_basis_def push_structure_def fimage.rep_eq fun_eq_iff)

definition finite_pair_syntax :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_pair_syntax R S=finite_syntax_join (Cons 2) (Cons 3) {|[],[0],[1]|}
    {|([],[0],[2]),([],[1],[3]),([0],[0],[1])|} R S"

lemma decode_finite_pair_syntax [simp]:
  "decode_finite_object (finite_pair_syntax R S)=pair_syntax (decode_finite_object R) (decode_finite_object S)"
  by (simp add: finite_pair_syntax_def decode_finite_syntax_join pair_syntax_def)

lemma syntax_prefix_code [code]:
  "syntax_prefix n a=(case a of [] \<Rightarrow> [n] | x#xs \<Rightarrow> if x=6 then a else n#a)"
  by (cases a) (auto simp: syntax_prefix_def)

definition finite_bound_pair_syntax :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_bound_pair_syntax R S=finite_syntax_join (syntax_prefix 2) (syntax_prefix 3) {|[],[0],[1]|}
    {|([],[0],[2]),([],[1],[3]),([0],[0],[1])|} R S"

lemma decode_finite_bound_pair_syntax [simp]:
  "decode_finite_object (finite_bound_pair_syntax R S)=bound_pair_syntax (decode_finite_object R) (decode_finite_object S)"
  by (simp add: finite_bound_pair_syntax_def decode_finite_syntax_join bound_pair_syntax_def)

definition finite_syntax_union :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_syntax_union R S=finite_syntax_join (Cons 2) (Cons 3) {||} {||} R S"

lemma decode_finite_syntax_union [simp]:
  "decode_finite_object (finite_syntax_union R S)=syntax_union (decode_finite_object R) (decode_finite_object S)"
  by (simp add: finite_syntax_union_def decode_finite_syntax_join syntax_union_def pair_syntax_def)

definition finite_bound_union :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_bound_union R S=finite_syntax_join (syntax_prefix 2) (syntax_prefix 3) {||} {||} R S"

lemma decode_finite_bound_union [simp]:
  "decode_finite_object (finite_bound_union R S)=bound_union (decode_finite_object R) (decode_finite_object S)"
  by (simp add: finite_bound_union_def decode_finite_syntax_join bound_union_def bound_pair_syntax_def)

fun finite_syntax_forest :: "finite_exact_artifact list \<Rightarrow> finite_exact_artifact" where
  "finite_syntax_forest []=finite_empty_artifact"
| "finite_syntax_forest (R#Rs)=finite_syntax_union R (finite_syntax_forest Rs)"

lemma decode_finite_syntax_forest [simp]:
  "decode_finite_object (finite_syntax_forest Rs)=syntax_forest (map decode_finite_object Rs)"
  by (induction Rs) simp_all

definition finite_attach_structure :: "finite_exact_artifact \<Rightarrow> local_address finite_rra_structure \<Rightarrow> finite_exact_artifact" where
  "finite_attach_structure R H=\<lparr>finite_structure=\<lparr>
    finite_carrier=finite_carrier (finite_structure R) |\<union>| finite_carrier H,
    finite_incidence=finite_incidence (finite_structure R) |\<union>| finite_incidence H\<rparr>,
    finite_data=finite_data R\<rparr>"

lemma decode_finite_attach_structure [simp]:
  "decode_finite_object (finite_attach_structure R H)=attach_structure (decode_finite_object R) (decode_finite_structure H)"
  by (simp add: finite_attach_structure_def attach_structure_def decode_finite_object_def decode_finite_structure_def)

definition finite_record_structure :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a finite_rra_structure" where
  "finite_record_structure r ps xs=\<lparr>finite_carrier=finsert r (fset_of_list ps |\<union>| fset_of_list xs),
    finite_incidence=fimage (\<lambda>(p,x). (r,p,x)) (fset_of_list (zip ps xs)) |\<union>|
      fimage (\<lambda>(p,q). (p,p,q)) (fset_of_list (zip ps (tl ps)))\<rparr>"

lemma decode_finite_record_structure [simp]:
  "decode_finite_structure (finite_record_structure r ps xs)=record_structure r ps xs"
  by (simp add: finite_record_structure_def record_structure_def decode_finite_structure_def
    fimage.rep_eq fset_of_list.rep_eq)

definition finite_record_wrapper :: "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow>
    local_address list \<Rightarrow> local_address list \<Rightarrow> finite_exact_artifact" where
  "finite_record_wrapper R r ps xs=finite_attach_structure R (finite_record_structure r ps xs)"

lemma decode_finite_record_wrapper [simp]:
  "decode_finite_object (finite_record_wrapper R r ps xs)=record_wrapper (decode_finite_object R) r ps xs"
  by (simp add: finite_record_wrapper_def record_wrapper_def)

definition finite_family_wrapper :: "finite_exact_artifact \<Rightarrow> local_address \<Rightarrow>
    (local_address\<times>local_address) fset \<Rightarrow> finite_exact_artifact" where
  "finite_family_wrapper R r M=finite_attach_structure R \<lparr>
    finite_carrier=finsert r (fimage fst M |\<union>| fimage snd M),
    finite_incidence=fimage (\<lambda>(p,x). (r,p,x)) M\<rparr>"

lemma decode_finite_family_wrapper [simp]:
  "decode_finite_object (finite_family_wrapper R r M)=family_wrapper (decode_finite_object R) r (fset M)"
  by (simp add: finite_family_wrapper_def family_wrapper_def family_object_def
    decode_finite_structure_def fimage.rep_eq rel_dom_image rel_ran_image)

definition finite_scope_wrapper :: "finite_exact_artifact \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> finite_exact_artifact" where
  "finite_scope_wrapper R V b r p q=finite_attach_structure R \<lparr>
    finite_carrier={|b,r,p,q|},finite_incidence={|(r,p,b),(r,q,[]),(p,p,q)|} |\<union>|
      fimage (\<lambda>a. (b,a,a)) V\<rparr>"

lemma decode_finite_scope_wrapper [simp]:
  "decode_finite_object (finite_scope_wrapper R V b r p q)=scope_wrapper (decode_finite_object R) (fset V) b r p q"
  by (simp add: finite_scope_wrapper_def decode_finite_structure_def attach_structure_def
    scope_wrapper_def fimage.rep_eq Un_assoc)

export_code finite_payload_syntax finite_literal_syntax finite_pair_syntax finite_bound_pair_syntax finite_syntax_forest
  finite_bound_union finite_record_wrapper finite_family_wrapper finite_scope_wrapper checking SML

text \<open>
  Executable inputs and results contain complete finite incidence and data.
  Each decoding equation identifies the existing structural constructor
  exactly. The four syntax joins share one finite operation. As in those
  existing constructors, joins have no counted data; wrappers preserve every
  original data component. These equations do not assert formation without
  the original constructors' prerequisites.
\<close>

end
