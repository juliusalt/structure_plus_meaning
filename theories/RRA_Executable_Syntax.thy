theory RRA_Executable_Syntax
  imports RRA_Finite_Environments RRA_Structural_Syntax
begin

section \<open>Complete finite incidence and data projections\<close>

lemma decode_finite_structure_fields [simp]:
  "rra_carrier (decode_finite_structure S)=fset (finite_carrier S)"
  "rra_incidence (decode_finite_structure S)=fset (finite_incidence S)"
  by (simp_all add: decode_finite_structure_def)

lemma decode_finite_object_selectors [simp]:
  "object_structure (decode_finite_object C) = decode_finite_structure (finite_structure C)"
  "object_data (decode_finite_object C) = decode_finite_basis (finite_data C)"
  by (simp_all add: decode_finite_object_def)

definition finite_headed_incidence :: "'a finite_rra_structure \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) fset" where
  "finite_headed_incidence S r =
    fimage (\<lambda>(h,p,x). (p,x)) (ffilter (\<lambda>(h,p,x). h=r) (finite_incidence S))"

lemma finite_headed_incidence_correct:
  "fset (finite_headed_incidence S r) = headed_incidence (decode_finite_structure S) r"
  by (auto simp: finite_headed_incidence_def headed_incidence_def decode_finite_structure_def
      fimage.rep_eq split: prod.splits; force)

definition finite_empty_basis :: "('a,'v) finite_opaque_basis" where
  "finite_empty_basis = \<lparr>finite_bag={#},finite_bindings={||}\<rparr>"

definition finite_payload_basis :: "'a \<Rightarrow> 'v \<Rightarrow> ('a,'v) finite_opaque_basis" where
  "finite_payload_basis a v = \<lparr>finite_bag={#},finite_bindings={|(a,v)|}\<rparr>"

definition finite_basis_slice :: "('a,'v) finite_opaque_basis \<Rightarrow> 'a fset \<Rightarrow> ('a,'v) finite_opaque_basis" where
  "finite_basis_slice D I =
    \<lparr>finite_bag=filter_mset (\<lambda>(a,v). a |\<in>| I) (finite_bag D),
     finite_bindings=ffilter (\<lambda>(a,v). a |\<in>| I) (finite_bindings D)\<rparr>"

lemma decode_finite_empty_basis [simp]: "decode_finite_basis finite_empty_basis = empty_basis"
  by (simp add: finite_empty_basis_def decode_finite_basis_def empty_basis_def fun_eq_iff)

lemma decode_finite_payload_basis [simp]:
  "decode_finite_basis (finite_payload_basis a v) =
    \<lparr>bag_count=(\<lambda>_. 0),functional_bindings={(a,v)}\<rparr>"
  by (simp add: finite_payload_basis_def decode_finite_basis_def fun_eq_iff)

lemma finite_basis_slice_correct:
  "decode_finite_basis (finite_basis_slice D I) = restrict_basis (fset I) (decode_finite_basis D)"
  by (auto simp: finite_basis_slice_def decode_finite_basis_def restrict_basis_def basis_identity
      fun_eq_iff split: prod.splits)

definition finite_data_empty_on :: "('a,'v) finite_structured_object \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "finite_data_empty_on C I \<longleftrightarrow> finite_basis_slice (finite_data C) I=finite_empty_basis"

lemma finite_data_empty_on_correct:
  "finite_data_empty_on C I \<longleftrightarrow> restrict_basis (fset I) (object_data (decode_finite_object C))=empty_basis"
  by (simp only: finite_data_empty_on_def decode_finite_object_selectors
      decode_finite_empty_basis[symmetric] finite_basis_slice_correct[symmetric] decode_finite_basis_injective)

definition finite_payload_at :: "('a,'v) finite_structured_object \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool" where
  "finite_payload_at C a v \<longleftrightarrow> finite_basis_slice (finite_data C) {|a|}=finite_payload_basis a v"

lemma finite_payload_at_correct:
  "finite_payload_at C a v \<longleftrightarrow> payload_at (decode_finite_object C) a v"
proof -
  have slice: "decode_finite_basis (finite_basis_slice (finite_data C) {|a|}) =
      restrict_basis {a} (object_data (decode_finite_object C))"
    by (simp add: finite_basis_slice_correct)
  show ?thesis
    by (simp only: finite_payload_at_def payload_at_def slice[symmetric]
        decode_finite_payload_basis[symmetric] decode_finite_basis_injective)
qed

definition finite_payload_leaf_at :: "('a,'v) finite_structured_object \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> bool" where
  "finite_payload_leaf_at C a v \<longleftrightarrow> finite_object_formed C \<and>
    finite_headed_incidence (finite_structure C) a={||} \<and> finite_payload_at C a v"

lemma finite_payload_leaf_at_correct:
  "finite_payload_leaf_at C a v \<longleftrightarrow> payload_leaf_at (decode_finite_object C) a v"
  by (simp add: finite_payload_leaf_at_def payload_leaf_at_def finite_object_formed_correct
      finite_payload_at_correct fset_inject[symmetric] finite_headed_incidence_correct)

section \<open>Complete families preserve every identified socket\<close>

definition finite_family_at ::
  "('a,'v) finite_structured_object \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a) fset \<Rightarrow> bool" where
  "finite_family_at C r M \<longleftrightarrow>
    finite_object_formed C \<and> r |\<in>| finite_carrier (finite_structure C) \<and>
    finite_headed_incidence (finite_structure C) r=M \<and> finite_relation_functional M \<and>
    r |\<notin>| fimage fst M \<and>
    fBall (fimage fst M) (\<lambda>p. finite_headed_incidence (finite_structure C) p={||}) \<and>
    finite_data_empty_on C (finsert r (fimage fst M))"

lemma finite_family_at_correct:
  "finite_family_at C r M \<longleftrightarrow> family_at (decode_finite_object C) r (fset M)"
  by (simp add: finite_family_at_def family_at_def finite_object_formed_correct
      finite_relation_functional_correct finite_data_empty_on_correct
      fset_inject[symmetric] finite_headed_incidence_correct rel_dom_image fimage.rep_eq
      decode_finite_structure_def)

section \<open>Record order is read from the actual successor incidence\<close>

definition finite_field_endpoint ::
  "'a finite_rra_structure \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "finite_field_endpoint S r p x \<longleftrightarrow>
    fimage snd (ffilter (\<lambda>(q,y). q=p) (finite_headed_incidence S r))={|x|}"

lemma finite_field_endpoint_correct:
  "finite_field_endpoint S r p x \<longleftrightarrow> field_endpoint (decode_finite_structure S) r p x"
proof -
  have fibre: "fset (fimage snd (ffilter (\<lambda>(q,y). q=p) (finite_headed_incidence S r))) =
      {y. (p,y) \<in> headed_incidence (decode_finite_structure S) r}"
    by (auto simp: fimage.rep_eq finite_headed_incidence_correct
        split: prod.splits intro: rev_image_eqI; force)
  show ?thesis
    by (simp only: finite_field_endpoint_def fset_inject[symmetric] fibre field_endpoint_from_head)
       simp
qed

lemma record_path_first:
  assumes "record_path S r p ps xs"
  shows "ps\<noteq>[] \<and> hd ps=p"
  using assms by (cases rule: record_path.cases) auto

lemma record_path_empty [simp]:
  "\<not> record_path S r p [] xs"
  "\<not> record_path S r p ps []"
  using record_path_nonempty record_path_lengths by fastforce+

lemma record_path_cons_iff:
  "record_path S r p (q#qs) (x#xs) \<longleftrightarrow>
    p=q \<and> q\<noteq>r \<and> field_endpoint S r q x \<and>
    ((qs=[] \<and> xs=[] \<and> headed_incidence S q={}) \<or>
      (qs\<noteq>[] \<and> headed_incidence S q={(q,hd qs)} \<and> record_path S r (hd qs) qs xs))"
proof
  assume path: "record_path S r p (q#qs) (x#xs)"
  show "p=q \<and> q\<noteq>r \<and> field_endpoint S r q x \<and>
    ((qs=[] \<and> xs=[] \<and> headed_incidence S q={}) \<or>
      (qs\<noteq>[] \<and> headed_incidence S q={(q,hd qs)} \<and> record_path S r (hd qs) qs xs))"
    using path by (cases rule: record_path.cases) (auto dest: record_path_first)
next
  assume rhs: "p=q \<and> q\<noteq>r \<and> field_endpoint S r q x \<and>
    ((qs=[] \<and> xs=[] \<and> headed_incidence S q={}) \<or>
      (qs\<noteq>[] \<and> headed_incidence S q={(q,hd qs)} \<and> record_path S r (hd qs) qs xs))"
  show "record_path S r p (q#qs) (x#xs)"
    using rhs by (cases "qs=[]") (auto intro: record_path.path_last record_path.path_slot)
qed

fun finite_record_path ::
  "'a finite_rra_structure \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "finite_record_path S r [] xs = False"
| "finite_record_path S r (p#ps) [] = False"
| "finite_record_path S r (p#ps) (x#xs) \<longleftrightarrow>
    p\<noteq>r \<and> finite_field_endpoint S r p x \<and>
    (if ps=[] then xs=[] \<and> finite_headed_incidence S p={||}
     else finite_headed_incidence S p={|(p,hd ps)|} \<and> finite_record_path S r ps xs)"

lemma finite_record_path_correct:
  "finite_record_path S r ps xs \<longleftrightarrow> record_path (decode_finite_structure S) r (hd ps) ps xs"
proof (induction ps arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  show ?case using Cons.IH
    by (cases xs) (auto simp: record_path_cons_iff finite_field_endpoint_correct
        fset_inject[symmetric] finite_headed_incidence_correct split: if_splits)
qed

definition finite_record_at ::
  "('a,'v) finite_structured_object \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "finite_record_at C r ps xs \<longleftrightarrow>
    finite_object_formed C \<and> r |\<in>| finite_carrier (finite_structure C) \<and>
    ((ps=[] \<and> xs=[] \<and> finite_headed_incidence (finite_structure C) r={||}) \<or>
     (finite_record_path (finite_structure C) r ps xs \<and>
       finite_headed_incidence (finite_structure C) r=fset_of_list (zip ps xs))) \<and>
    finite_data_empty_on C (finsert r (fset_of_list ps))"

theorem finite_record_at_correct:
  "finite_record_at C r ps xs \<longleftrightarrow> record_at (decode_finite_object C) r ps xs"
  by (simp add: finite_record_at_def record_at_def raw_record_at_def finite_object_formed_correct
      finite_record_path_correct finite_data_empty_on_correct
      fset_inject[symmetric] finite_headed_incidence_correct decode_finite_structure_def fset_of_list.rep_eq)

lemma record_head_card:
  assumes rec: "record_at C r ps xs"
  shows "card (headed_incidence (object_structure C) r)=length xs"
proof -
  have len: "length ps=length xs" and dist: "distinct ps"
    using record_at_preserves_socket_occurrences[OF rec] by auto
  have head: "headed_incidence (object_structure C) r=set (zip ps xs)"
    using rec by (auto simp: record_at_def raw_record_at_def)
  have zip: "distinct (zip ps xs)" by (rule distinct_zipI1[OF dist])
  show ?thesis by (simp add: head distinct_card[OF zip] len)
qed

export_code finite_headed_incidence finite_basis_slice finite_payload_at
  finite_payload_leaf_at finite_family_at finite_record_at checking SML

text \<open>
  These checks inspect the complete supplied incidence at each selected head
  and the complete attached data on the grammar's interior. Record order
  follows successor incidence. Family sockets remain an unordered finite
  relation with their actual identities. The correspondence equations cover
  malformed finite inputs as well as formed artifacts.
\<close>

end
