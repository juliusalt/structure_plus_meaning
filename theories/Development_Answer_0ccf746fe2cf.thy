theory Development_Answer_0ccf746fe2cf
  imports Finite_Sorted_Set_Execution Finite_Ordered_Relation_Checks Finite_Relation_Functionality_Execution Finite_Collection_Equality_Execution RRA_Ordered_Artifact_Formation Factor_Ordered_Target_Equality Factor_Finite_Accumulated_Data_Syntax Finite_Investigation_Execution_Sharing Shared_Investigation_Cycles Finite_Prepared_Reader_Inspections Parallel_Assessment_Execution Complete_Object_References Ordered_Environment_Artifact_Objects Prepared_Computed_Functions Complete_Term_References Finite_Collection_Subset_Execution Finite_Filtered_Keyed_Products RRA_Linked_Record_Candidates Finite_Investigation_Basis_Sharing Factor_Finite_Judgment_Reading_Sharing Factor_Invariant_Evaluation_Sharing Factor_Formation_Once_Readings Factor_Join_Reading_Conditions Factor_Recovered_Graph_Sharing Parallel_Presented_Investigations Indexed_Term_Words Ordered_Term_Comparison Factor_Policy_Scope_Sharing Factor_Formation_Once_Definitions Factor_Complete_Data_Walks Finite_Ordered_Set_Difference Factor_Ordered_Generation_Checking Ordered_Term_Demands Isabelle_Constant_Closure
begin

local_setup \<open>Isabelle_Constant_Closure.note_code_equations \<^binding>\<open>development_demanded_code\<close>
  "Factor_Complete_Data_Walks.finite_data_walk"\<close>

section \<open>The walk reads an artifact through four readers\<close>

text \<open>
  Every step of the complete data walk reads the artifact only through the incidence rows headed
  at an address, the functional values attached there, whether a counted value is attached there,
  and membership in the carrier. The walk is stated once over those readers; supplied with the
  artifact's own readers it is the existing walk.
\<close>

definition leaf_values_read ::
  "(local_address \<Rightarrow> (local_address\<times>local_address) fset) \<Rightarrow> (local_address \<Rightarrow> octets fset) \<Rightarrow>
    (local_address \<Rightarrow> bool) \<Rightarrow> local_address \<Rightarrow> octets fset" where
  "leaf_values_read heads values counted r=
    ffilter (\<lambda>v. heads r={||} \<and> \<not>counted r \<and> values r={|v|}) (values r)"

primrec record_path_read :: "(local_address \<Rightarrow> (local_address\<times>local_address) fset) \<Rightarrow>
    local_address \<Rightarrow> local_address list \<Rightarrow> local_address list \<Rightarrow> bool" where
  "record_path_read heads r [] xs=False"
| "record_path_read heads r (p#ps) xs=(case xs of [] \<Rightarrow> False | x#ys \<Rightarrow>
    p\<noteq>r \<and> fimage snd (ffilter (\<lambda>(q,y). q=p) (heads r))={|x|} \<and>
    (if ps=[] then ys=[] \<and> heads p={||}
     else heads p={|(p,hd ps)|} \<and> record_path_read heads r ps ys))"

definition record_body_read ::
  "(local_address \<Rightarrow> (local_address\<times>local_address) fset) \<Rightarrow> (local_address \<Rightarrow> octets fset) \<Rightarrow>
    (local_address \<Rightarrow> bool) \<Rightarrow> (local_address \<Rightarrow> bool) \<Rightarrow>
    local_address \<Rightarrow> local_address list \<Rightarrow> local_address list \<Rightarrow> bool" where
  "record_body_read heads values counted member r ps xs=(member r \<and>
    ((ps=[] \<and> xs=[] \<and> heads r={||}) \<or>
     (record_path_read heads r ps xs \<and> heads r=fset_of_list (zip ps xs))) \<and>
    list_all (\<lambda>a. \<not>counted a \<and> values a={||}) (r#ps))"

definition record_candidates_read ::
  "(local_address \<Rightarrow> (local_address\<times>local_address) fset) \<Rightarrow> (local_address \<Rightarrow> octets fset) \<Rightarrow>
    (local_address \<Rightarrow> bool) \<Rightarrow> (local_address \<Rightarrow> bool) \<Rightarrow>
    local_address \<Rightarrow> nat \<Rightarrow> (local_address list\<times>local_address list) fset" where
  "record_candidates_read heads values counted member r n=(let H=heads r in
    if fcard H=n then ffilter (\<lambda>(ps,xs). record_body_read heads values counted member r ps xs)
      (fimage (\<lambda>rows. (map fst rows,map snd rows)) (finite_lists_of_length n H)) else {||})"

primrec data_walk_read ::
  "(local_address \<Rightarrow> (local_address\<times>local_address) fset) \<Rightarrow> (local_address \<Rightarrow> octets fset) \<Rightarrow>
    (local_address \<Rightarrow> bool) \<Rightarrow> (local_address \<Rightarrow> bool) \<Rightarrow>
    nat \<Rightarrow> local_address \<Rightarrow> (finite_factor_term\<times>local_address list) option" where
  "data_walk_read heads values counted member 0 r=None"
| "data_walk_read heads values counted member (Suc n) r=
    (case sorted_list_of_fset (leaf_values_read heads values counted r) of
      v#vs \<Rightarrow> Some (Finite_Payload v,[r])
    | [] \<Rightarrow> (case sorted_list_of_fset (record_candidates_read heads values counted member r 2) of
        (ps,xs)#rest \<Rightarrow> (case xs of
            [l,q] \<Rightarrow> (case data_walk_read heads values counted member n l of None \<Rightarrow> None
              | Some (x,ls) \<Rightarrow> (case data_walk_read heads values counted member n q of None \<Rightarrow> None
                | Some (y,qs) \<Rightarrow> Some (Finite_Pair x y,r#ps@ls@qs)))
          | _ \<Rightarrow> None)
      | [] \<Rightarrow> None))"

lemma finite_slice_at_iff:
  "finite_basis_slice D {|a|}=\<lparr>finite_bag=M,finite_bindings=F\<rparr> \<longleftrightarrow>
    filter_mset (\<lambda>(b,v). b=a) (finite_bag D)=M \<and> ffilter (\<lambda>(b,v). b=a) (finite_bindings D)=F"
  by (simp add: finite_basis_slice_def)

lemma counted_slice_empty:
  "filter_mset (\<lambda>(b,v). b=a) M={#} \<longleftrightarrow> \<not>(\<exists>v. (a,v) \<in># M)"
proof
  assume empty: "filter_mset (\<lambda>(b,v). b=a) M={#}"
  show "\<not>(\<exists>v. (a,v) \<in># M)"
  proof
    assume "\<exists>v. (a,v) \<in># M"
    then obtain v where member: "(a,v) \<in># M" ..
    have "(a,v) \<in># filter_mset (\<lambda>(b,v). b=a) M" using member by simp
    then show False by (simp only: empty) simp
  qed
next
  assume none: "\<not>(\<exists>v. (a,v) \<in># M)"
  show "filter_mset (\<lambda>(b,v). b=a) M={#}"
  proof (rule multiset_eqI)
    fix z :: "'a\<times>'b"
    obtain b w where z: "z=(b,w)" by (cases z)
    show "count (filter_mset (\<lambda>(b,v). b=a) M) z=count {#} z"
    proof (cases "b=a")
      case True
      then have "z \<notin># M" using none z by blast
      then show ?thesis by (simp add: not_in_iff)
    next
      case False
      then show ?thesis by (simp add: z)
    qed
  qed
qed

lemma binding_slice_singleton:
  "ffilter (\<lambda>(b,w). b=a) (finite_bindings (finite_data C))={|(a,v)|} \<longleftrightarrow> finite_payload_values C a={|v|}"
proof -
  have left: "ffilter (\<lambda>(b,w). b=a) (finite_bindings (finite_data C))={|(a,v)|} \<longleftrightarrow>
      (\<forall>w. (a,w) |\<in>| finite_bindings (finite_data C) \<longleftrightarrow> w=v)"
  proof
    assume slice: "ffilter (\<lambda>(b,w). b=a) (finite_bindings (finite_data C))={|(a,v)|}"
    show "\<forall>w. (a,w) |\<in>| finite_bindings (finite_data C) \<longleftrightarrow> w=v"
    proof
      fix w
      have "(a,w) |\<in>| ffilter (\<lambda>(b,w). b=a) (finite_bindings (finite_data C)) \<longleftrightarrow>
          (a,w) |\<in>| finite_bindings (finite_data C)" by simp
      then show "(a,w) |\<in>| finite_bindings (finite_data C) \<longleftrightarrow> w=v" by (simp add: slice)
    qed
  next
    assume attached: "\<forall>w. (a,w) |\<in>| finite_bindings (finite_data C) \<longleftrightarrow> w=v"
    show "ffilter (\<lambda>(b,w). b=a) (finite_bindings (finite_data C))={|(a,v)|}"
    proof (rule fset_eqI)
      fix z :: "'a\<times>'b"
      obtain b w where z: "z=(b,w)" by (cases z)
      show "z |\<in>| ffilter (\<lambda>(b,w). b=a) (finite_bindings (finite_data C)) \<longleftrightarrow> z |\<in>| {|(a,v)|}"
        using attached by (cases "b=a") (simp_all add: z)
    qed
  qed
  have right: "finite_payload_values C a={|v|} \<longleftrightarrow>
      (\<forall>w. (a,w) |\<in>| finite_bindings (finite_data C) \<longleftrightarrow> w=v)"
    by (simp only: fset_eq_iff finite_payload_values_member finsert_iff fempty_iff simp_thms)
  show ?thesis by (simp only: left right)
qed

lemma finite_payload_at_read:
  "finite_payload_at C a v \<longleftrightarrow>
    filter_mset (\<lambda>(b,w). b=a) (finite_bag (finite_data C))={#} \<and> finite_payload_values C a={|v|}"
  by (simp only: finite_payload_at_def finite_payload_basis_def finite_slice_at_iff binding_slice_singleton)

lemma finite_slice_empty_read:
  "finite_basis_slice (finite_data C) {|a|}=finite_empty_basis \<longleftrightarrow>
    filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))={#} \<and> finite_payload_values C a={||}"
proof -
  have bindings: "ffilter (\<lambda>(b,v). b=a) (finite_bindings (finite_data C))={||} \<longleftrightarrow> finite_payload_values C a={||}"
    by (simp add: finite_payload_values_def)
  show ?thesis
    by (simp only: finite_empty_basis_def finite_slice_at_iff bindings)
qed

lemma leaf_values_read_artifact:
  "leaf_values_read (finite_headed_incidence (finite_structure C)) (finite_payload_values C) (\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#}) r=
    finite_data_leaf_values C r"
  unfolding leaf_values_read_def finite_data_leaf_values_def
  by (rule ffilter_member_cong) (simp only: finite_payload_leaf_body_def finite_payload_at_read not_not)

lemma record_path_read_artifact:
  "record_path_read (finite_headed_incidence S) r ps xs=finite_record_path S r ps xs"
proof (induction ps arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  show ?case by (cases xs) (simp_all add: finite_field_endpoint_def Cons.IH)
qed

lemma finite_data_empty_on_points:
  "finite_data_empty_on C (fset_of_list as) \<longleftrightarrow>
    list_all (\<lambda>a. finite_basis_slice (finite_data C) {|a|}=finite_empty_basis) as"
proof -
  have slice: "finite_basis_slice D I=finite_empty_basis \<longleftrightarrow>
      (\<forall>x. x \<in># finite_bag D \<longrightarrow> fst x |\<notin>| I) \<and> (\<forall>x. x |\<in>| finite_bindings D \<longrightarrow> fst x |\<notin>| I)"
    for D :: "('a,'v) finite_opaque_basis" and I
    by (auto simp: finite_basis_slice_def finite_empty_basis_def fset_eq_iff split_beta)
  have "finite_data_empty_on C (fset_of_list as) \<longleftrightarrow>
      (\<forall>x. x \<in># finite_bag (finite_data C) \<longrightarrow> fst x \<notin> set as) \<and>
      (\<forall>x. x |\<in>| finite_bindings (finite_data C) \<longrightarrow> fst x \<notin> set as)"
    by (simp only: finite_data_empty_on_def slice fset_of_list_elem)
  also have "\<dots> \<longleftrightarrow> list_all (\<lambda>a. finite_basis_slice (finite_data C) {|a|}=finite_empty_basis) as"
    by (simp only: slice list_all_iff finsert_iff fempty_iff simp_thms) blast
  finally show ?thesis .
qed

lemma record_body_read_artifact:
  "record_body_read (finite_headed_incidence (finite_structure C)) (finite_payload_values C) (\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#})
    (\<lambda>a. a |\<in>| finite_carrier (finite_structure C)) r ps xs=finite_record_body C r ps xs"
proof -
  have empty: "finite_data_empty_on C (finsert r (fset_of_list ps)) \<longleftrightarrow>
      list_all (\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))={#} \<and>
        finite_payload_values C a={||}) (r#ps)"
    using finite_data_empty_on_points[of C "r#ps"] by (simp only: fset_of_list_simps finite_slice_empty_read)
  show ?thesis
    by (simp only: record_body_read_def finite_record_body_def record_path_read_artifact empty not_not)
qed

lemma record_candidates_read_artifact:
  "record_candidates_read (finite_headed_incidence (finite_structure C)) (finite_payload_values C) (\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#})
    (\<lambda>a. a |\<in>| finite_carrier (finite_structure C)) r n=finite_record_body_candidates C r n"
  by (simp only: record_candidates_read_def finite_record_body_candidates_def record_body_read_artifact)

theorem data_walk_read_artifact:
  "data_walk_read (finite_headed_incidence (finite_structure C)) (finite_payload_values C) (\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#})
    (\<lambda>a. a |\<in>| finite_carrier (finite_structure C)) n r=finite_data_walk n C r"
  by (induction n arbitrary: r) (simp_all only: data_walk_read.simps finite_data_walk.simps
    leaf_values_read_artifact record_candidates_read_artifact)

section \<open>The readers of an artifact are the existing indexes, built once\<close>

text \<open>
  Each reader is a relation keyed by an address: the incidence rows by their head, the functional
  and the counted attachments by their atom. The existing relation store holds each of them under
  the address's existing binary path, and the existing ordered member index holds the carrier, so
  every reading is one lookup instead of a scan of the whole artifact.
\<close>

lemma address_binary_path_inj: "inj address_binary_path"
  by (rule injI) simp

lemma address_relation_store_member:
  "v |\<in>| relation_store_lookup (relation_store (map (map_prod address_binary_path id) rows))
      (address_binary_path a) \<longleftrightarrow> (a,v)\<in>set rows"
proof -
  have injective: "inj (map_prod address_binary_path (id::'v\<Rightarrow>'v))"
  proof -
    have "inj_on (map_prod address_binary_path (id::'v\<Rightarrow>'v)) (UNIV\<times>UNIV)"
      by (rule map_prod_inj_on[OF address_binary_path_inj inj_on_id])
    then show ?thesis by simp
  qed
  have key: "(address_binary_path a,v)=map_prod address_binary_path id (a,v)" by simp
  show ?thesis
    by (simp only: relation_store_member key set_map inj_image_mem_iff[OF injective])
qed

lemma indexed_heads_exact:
  "relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_fset (finite_incidence S)))) (address_binary_path a)=finite_headed_incidence S a"
proof (rule fset_eqI)
  fix z :: "local_address\<times>local_address"
  have "z |\<in>| finite_headed_incidence S a \<longleftrightarrow> (a,z) |\<in>| finite_incidence S"
    by (cases z) (simp add: finite_headed_incidence_correct decode_finite_structure_def)
  then show "z |\<in>| relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_fset (finite_incidence S)))) (address_binary_path a) \<longleftrightarrow> z |\<in>| finite_headed_incidence S a"
    by (simp only: address_relation_store_member sorted_list_of_fset_simps)
qed

lemma indexed_values_exact:
  "relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_fset (finite_bindings (finite_data C))))) (address_binary_path a)=finite_payload_values C a"
  by (rule fset_eqI) (simp only: address_relation_store_member sorted_list_of_fset_simps finite_payload_values_member)

lemma indexed_counted_exact:
  "relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_multiset (finite_bag (finite_data C))))) (address_binary_path a)\<noteq>{||} \<longleftrightarrow>
    filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#}"
proof -
  have "relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_multiset (finite_bag (finite_data C))))) (address_binary_path a)\<noteq>{||} \<longleftrightarrow>
    (\<exists>v. (a,v) \<in># finite_bag (finite_data C))"
    by (simp only: fset_eq_iff fempty_iff address_relation_store_member set_sorted_list_of_multiset simp_thms)
      blast
  then show ?thesis by (simp only: counted_slice_empty not_not)
qed

definition indexed_data_walk :: "finite_exact_artifact \<Rightarrow> nat \<Rightarrow> local_address \<Rightarrow>
    (finite_factor_term\<times>local_address list) option" where
  "indexed_data_walk C n r=(let
    H=relation_store (map (map_prod address_binary_path id) (sorted_list_of_fset (finite_incidence (finite_structure C))));
    F=relation_store (map (map_prod address_binary_path id) (sorted_list_of_fset (finite_bindings (finite_data C))));
    B=relation_store (map (map_prod address_binary_path id) (sorted_list_of_multiset (finite_bag (finite_data C))));
    M=ordered_member_tree (finite_carrier (finite_structure C)) in
    data_walk_read (\<lambda>a. relation_store_lookup H (address_binary_path a))
      (\<lambda>a. relation_store_lookup F (address_binary_path a))
      (\<lambda>a. relation_store_lookup B (address_binary_path a)\<noteq>{||}) (\<lambda>a. RBT.lookup M a\<noteq>None) n r)"

theorem indexed_data_walk_exact: "indexed_data_walk C n r=finite_data_walk n C r"
proof -
  have heads: "(\<lambda>a. relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_fset (finite_incidence (finite_structure C))))) (address_binary_path a))=(finite_headed_incidence (finite_structure C))"
    by (rule ext) (rule indexed_heads_exact)
  have attached: "(\<lambda>a. relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_fset (finite_bindings (finite_data C))))) (address_binary_path a))=finite_payload_values C"
    by (rule ext) (rule indexed_values_exact)
  have counted: "(\<lambda>a. relation_store_lookup (relation_store (map (map_prod address_binary_path id)
      (sorted_list_of_multiset (finite_bag (finite_data C))))) (address_binary_path a)\<noteq>{||})=(\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#})"
    by (rule ext) (rule indexed_counted_exact)
  have member: "(\<lambda>a. RBT.lookup (ordered_member_tree (finite_carrier (finite_structure C))) a\<noteq>None)=
      (\<lambda>a. a |\<in>| finite_carrier (finite_structure C))"
    by (rule ext) (simp only: ordered_member_tree_exact)
  show ?thesis
    by (simp only: indexed_data_walk_def Let_def heads attached counted member data_walk_read_artifact)
qed

declare [[code drop: Factor_Complete_Data_Walks.finite_data_walk]]

lemma development_answer [code]:
  "finite_data_walk n C r=indexed_data_walk C n r"
  by (rule indexed_data_walk_exact[symmetric])

end
