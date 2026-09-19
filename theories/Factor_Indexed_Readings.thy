theory Factor_Indexed_Readings
  imports Factor_Formation_Once_Definitions Factor_Demanded_Package_Readings
    Development_Answer_0ccf746fe2cf
begin

section \<open>An artifact is asked through its reading\<close>

text \<open>
  Every syntax reading of an artifact asks it the same few questions at an address: the incidence
  rows headed there, the functional values attached there, whether a counted value is attached
  there and whether the address belongs to the carrier; pattern and term readings also bound their
  recursion by the size of the carrier. The reading of an artifact collects these answers. Asked by
  scanning, every question traverses the whole artifact, so reading a program of n clauses asks
  O(n) questions of an artifact of O(n) addresses. The existing indexes answer the same questions
  once they are built for the artifact: the address-keyed relation stores and the ordered member
  index the complete data walk reads through. The two readings are equal.
\<close>

record artifact_reading =
  reading_heads :: "local_address \<Rightarrow> (local_address\<times>local_address) fset"
  reading_values :: "local_address \<Rightarrow> octets fset"
  reading_counted :: "local_address \<Rightarrow> bool"
  reading_member :: "local_address \<Rightarrow> bool"
  reading_size :: nat

definition scanned_artifact_reading :: "finite_exact_artifact \<Rightarrow> artifact_reading" where
  "scanned_artifact_reading C=\<lparr>reading_heads=finite_headed_incidence (finite_structure C),
    reading_values=finite_payload_values C,
    reading_counted=(\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#}),
    reading_member=(\<lambda>a. a |\<in>| finite_carrier (finite_structure C)),
    reading_size=fcard (finite_carrier (finite_structure C))\<rparr>"

lemma scanned_artifact_reading_fields:
  "reading_heads (scanned_artifact_reading C)=finite_headed_incidence (finite_structure C)"
  "reading_values (scanned_artifact_reading C)=finite_payload_values C"
  "reading_counted (scanned_artifact_reading C)=(\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))\<noteq>{#})"
  "reading_member (scanned_artifact_reading C)=(\<lambda>a. a |\<in>| finite_carrier (finite_structure C))"
  "reading_size (scanned_artifact_reading C)=fcard (finite_carrier (finite_structure C))"
  by (simp_all add: scanned_artifact_reading_def)

definition indexed_artifact_reading :: "finite_exact_artifact \<Rightarrow> artifact_reading" where
  "indexed_artifact_reading C=(let
    H=relation_store (map (map_prod address_binary_path id) (sorted_list_of_fset (finite_incidence (finite_structure C))));
    F=relation_store (map (map_prod address_binary_path id) (sorted_list_of_fset (finite_bindings (finite_data C))));
    B=relation_store (map (map_prod address_binary_path id) (sorted_list_of_multiset (finite_bag (finite_data C))));
    M=ordered_member_tree (finite_carrier (finite_structure C)) in
    \<lparr>reading_heads=(\<lambda>a. relation_store_lookup H (address_binary_path a)),
     reading_values=(\<lambda>a. relation_store_lookup F (address_binary_path a)),
     reading_counted=(\<lambda>a. relation_store_lookup B (address_binary_path a)\<noteq>{||}),
     reading_member=(\<lambda>a. RBT.lookup M a\<noteq>None),
     reading_size=length (sorted_list_of_fset (finite_carrier (finite_structure C)))\<rparr>)"

theorem indexed_artifact_reading_exact: "indexed_artifact_reading C=scanned_artifact_reading C"
proof -
  have size: "length (sorted_list_of_fset A)=fcard A" for A :: "local_address fset"
    by (simp add: sorted_list_of_fset.rep_eq fcard.rep_eq)
  show ?thesis
    by (simp add: indexed_artifact_reading_def scanned_artifact_reading_def Let_def fun_eq_iff
      indexed_heads_exact indexed_values_exact indexed_counted_exact ordered_member_tree_exact ordered_member_tree_some size)
qed

lemma indexed_artifact_reading_function: "indexed_artifact_reading=scanned_artifact_reading"
  by (rule ext) (rule indexed_artifact_reading_exact)

text \<open>
  The adopted answer for the complete data walk builds these four indexes for the walk's readers; they
  are the fields of the indexed reading, so the walk takes that reading and the indexes of an artifact
  are built in one place.
\<close>

lemma indexed_data_walk_reading_code [code]:
  "indexed_data_walk C n r=(let R=indexed_artifact_reading C in
    data_walk_read (reading_heads R) (reading_values R) (reading_counted R) (reading_member R) n r)"
  by (simp only: Let_def indexed_data_walk_exact indexed_artifact_reading_exact scanned_artifact_reading_fields
    data_walk_read_artifact)

section \<open>The syntax bodies of an artifact are stated once over its reading\<close>

text \<open>
  Each body below is the existing formation-free body with every question to the artifact asked
  of a reading; supplied with the artifact's scanned reading it is the existing body, and supplied
  with the indexed reading it computes the same value through the indexes.
\<close>

definition read_field_endpoint :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> bool" where
  "read_field_endpoint R r p x \<longleftrightarrow> fimage snd (ffilter (\<lambda>(q,y). q=p) (reading_heads R r))={|x|}"

fun read_record_path :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> local_address list \<Rightarrow> local_address list \<Rightarrow> bool" where
  "read_record_path R r [] xs=False"
| "read_record_path R r (p#ps) []=False"
| "read_record_path R r (p#ps) (x#xs) \<longleftrightarrow>
    p\<noteq>r \<and> read_field_endpoint R r p x \<and>
    (if ps=[] then xs=[] \<and> reading_heads R p={||}
     else reading_heads R p={|(p,hd ps)|} \<and> read_record_path R r ps xs)"

definition read_empty_on :: "artifact_reading \<Rightarrow> local_address fset \<Rightarrow> bool" where
  "read_empty_on R I \<longleftrightarrow> fBall I (\<lambda>a. \<not>reading_counted R a \<and> reading_values R a={||})"

definition read_payload_at :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> octets \<Rightarrow> bool" where
  "read_payload_at R a v \<longleftrightarrow> \<not>reading_counted R a \<and> reading_values R a={|v|}"

definition read_record_body :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> local_address list \<Rightarrow> local_address list \<Rightarrow> bool" where
  "read_record_body R r ps xs \<longleftrightarrow> reading_member R r \<and>
    ((ps=[] \<and> xs=[] \<and> reading_heads R r={||}) \<or>
     (read_record_path R r ps xs \<and> reading_heads R r=fset_of_list (zip ps xs))) \<and>
    read_empty_on R (finsert r (fset_of_list ps))"

definition read_record_successors :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> local_address fset" where
  "read_record_successors R p=fimage snd (ffilter (\<lambda>(q,y). q=p) (reading_heads R p))"

fun read_linked_rows :: "artifact_reading \<Rightarrow> (local_address\<times>local_address) fset \<Rightarrow> nat \<Rightarrow> local_address \<Rightarrow>
    (local_address\<times>local_address) list fset" where
  "read_linked_rows R H 0 p={||}"
| "read_linked_rows R H (Suc n) p=ffUnion (fimage (\<lambda>(q,x). if n=0 then {|[(q,x)]|}
      else fimage (Cons (q,x)) (ffUnion (fimage (read_linked_rows R H n) (read_record_successors R q))))
    (ffilter (\<lambda>(q,x). q=p) H))"

definition read_linked_record_rows :: "artifact_reading \<Rightarrow> (local_address\<times>local_address) fset \<Rightarrow> nat \<Rightarrow>
    (local_address\<times>local_address) list fset" where
  "read_linked_record_rows R H n=(if n=0 then {|[]|}
    else ffUnion (fimage (\<lambda>(p,x). read_linked_rows R H n p) H))"

definition read_record_candidates :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> nat \<Rightarrow> (local_address list\<times>local_address list) fset" where
  "read_record_candidates R r n=(let H=reading_heads R r in
    if fcard H=n then ffilter (\<lambda>(ps,xs). read_record_body R r ps xs)
      (fimage (\<lambda>rows. (map fst rows,map snd rows)) (read_linked_record_rows R H n))
    else {||})"

definition read_payload_leaf_body :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> octets \<Rightarrow> bool" where
  "read_payload_leaf_body R a v \<longleftrightarrow> reading_heads R a={||} \<and> read_payload_at R a v"

definition read_payload_readings :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> finite_factor_term finite_syntax_reading fset" where
  "read_payload_readings R r=fimage (\<lambda>v. (Finite_Payload v,{|r|},{||}))
    (ffilter (read_payload_leaf_body R r) (reading_values R r))"

fun read_raw_citation_at :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> citation \<Rightarrow> local_address fset \<Rightarrow> bool" where
  "read_raw_citation_at R r (Local a) I \<longleftrightarrow> reading_heads R r={|(r,a)|} \<and> I={|r|}"
| "read_raw_citation_at R r Local_Whole I \<longleftrightarrow> reading_heads R r={||} \<and> I={|r|}"
| "read_raw_citation_at R r (External_Whole k) I \<longleftrightarrow> r\<noteq>k \<and> reading_heads R r={|(k,k)|} \<and> I={|r|}"
| "read_raw_citation_at R r (External k a) I \<longleftrightarrow>
    fBex (reading_heads R r) (\<lambda>(p,d).
      p=k \<and> distinct [r,k,d] \<and> reading_heads R r={|(r,k),(k,d)|} \<and>
      reading_heads R d={||} \<and> read_payload_at R d a \<and> I={|r,d|})"

definition read_citation_choices :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> (citation\<times>local_address fset) fset" where
  "read_citation_choices R r={|(Local_Whole,{|r|})|} |\<union>|
    fimage (\<lambda>(p,a). (Local a,{|r|})) (reading_heads R r) |\<union>|
    fimage (\<lambda>(k,x). (External_Whole k,{|r|})) (reading_heads R r) |\<union>|
    ffUnion (fimage (\<lambda>(k,d). fimage (\<lambda>a. (External k a,{|r,d|})) (reading_values R d)) (reading_heads R r))"

definition read_citation_candidates :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> (citation\<times>local_address fset) fset" where
  "read_citation_candidates R r=(if reading_member R r \<and> read_empty_on R {|r|}
    then ffilter (\<lambda>(c,I). read_raw_citation_at R r c I) (read_citation_choices R r) else {||})"

definition read_family_body_at :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> (local_address\<times>local_address) fset \<Rightarrow> bool" where
  "read_family_body_at R r M \<longleftrightarrow> reading_member R r \<and> reading_heads R r=M \<and> finite_relation_functional M \<and>
    r |\<notin>| fimage fst M \<and> fBall (fimage fst M) (\<lambda>p. reading_heads R p={||}) \<and>
    read_empty_on R (finsert r (fimage fst M))"

definition read_family_candidates :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> (local_address\<times>local_address) fset fset" where
  "read_family_candidates R r=(let H=reading_heads R r in if read_family_body_at R r H then {|H|} else {||})"

definition read_binder_scope_candidates :: "artifact_reading \<Rightarrow> local_address \<Rightarrow> local_address fset fset" where
  "read_binder_scope_candidates R b=(let V=fimage fst (reading_heads R b) in
    if read_family_body_at R b (fimage (\<lambda>a. (a,a)) V) then {|V|} else {||})"

definition read_two_field_record where
  "read_two_field_record R r F=ffUnion (fimage (\<lambda>(ps,xs).
    case xs of [l,q] \<Rightarrow> F ps l q | _ \<Rightarrow> {||}) (read_record_candidates R r 2))"

definition read_three_field_record where
  "read_three_field_record R r F=ffUnion (fimage
    (\<lambda>(ps,xs). finite_three_fields xs (F ps)) (read_record_candidates R r 3))"

definition read_record_readings where
  "read_record_readings R r f V reads=read_two_field_record R r
    (\<lambda>ps l q. finite_join_readings f V r ps (reads l) (reads q))"

definition read_variable_readings where
  "read_variable_readings R V r=ffUnion (fimage (finite_variable_leaf V) (read_citation_candidates R r))"

definition read_target_readings where
  "read_target_readings E u R r=ffUnion (fimage (\<lambda>(c,I).
    if finite_citation_slots c={||} then {||}
    else fimage (\<lambda>T. (Finite_Target T,I,finite_citation_slots c)) (finite_citation_targets E u c))
      (read_citation_candidates R r))"

section \<open>Supplied with the scanned reading, each body is the existing one\<close>

lemma finite_data_empty_on_read:
  "finite_data_empty_on C I \<longleftrightarrow> fBall I (\<lambda>a. filter_mset (\<lambda>(b,v). b=a) (finite_bag (finite_data C))={#} \<and>
    finite_payload_values C a={||})"
proof -
  obtain as where listed: "fset_of_list as=I" using exists_fset_of_list by blast
  show ?thesis
    unfolding listed[symmetric] finite_data_empty_on_points
    by (auto simp: list_all_iff finite_slice_empty_read fset_of_list.rep_eq)
qed

lemma read_empty_on_scanned: "read_empty_on (scanned_artifact_reading C) I \<longleftrightarrow> finite_data_empty_on C I"
  by (simp only: read_empty_on_def scanned_artifact_reading_fields finite_data_empty_on_read not_not)

lemma read_payload_at_scanned: "read_payload_at (scanned_artifact_reading C) a v \<longleftrightarrow> finite_payload_at C a v"
  by (simp only: read_payload_at_def scanned_artifact_reading_fields finite_payload_at_read not_not)

lemma read_field_endpoint_scanned:
  "read_field_endpoint (scanned_artifact_reading C)=finite_field_endpoint (finite_structure C)"
  by (simp add: fun_eq_iff read_field_endpoint_def finite_field_endpoint_def scanned_artifact_reading_fields)

lemma read_record_path_scanned:
  "read_record_path (scanned_artifact_reading C) r ps xs \<longleftrightarrow> finite_record_path (finite_structure C) r ps xs"
proof (induction ps arbitrary: xs)
  case Nil
  show ?case by simp
next
  case (Cons p ps)
  show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x ys)
    have previous: "read_record_path (scanned_artifact_reading C) r ps ys \<longleftrightarrow>
        finite_record_path (finite_structure C) r ps ys" by (rule Cons.IH)
    show ?thesis
      by (simp only: Cons read_record_path.simps finite_record_path.simps previous
        read_field_endpoint_scanned scanned_artifact_reading_fields)
  qed
qed

lemma read_record_body_scanned:
  "read_record_body (scanned_artifact_reading C) r ps xs \<longleftrightarrow> finite_record_body C r ps xs"
  by (simp only: read_record_body_def finite_record_body_def read_record_path_scanned read_empty_on_scanned
    scanned_artifact_reading_fields)

lemma read_record_successors_scanned:
  "read_record_successors (scanned_artifact_reading C)=finite_record_successors (finite_structure C)"
  by (simp add: fun_eq_iff read_record_successors_def finite_record_successors_def scanned_artifact_reading_fields)

lemma read_linked_rows_scanned:
  "read_linked_rows (scanned_artifact_reading C) H n=finite_linked_rows (finite_structure C) H n"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  show ?case
    by (rule ext) (simp only: read_linked_rows.simps finite_linked_rows.simps Suc.IH read_record_successors_scanned)
qed

lemma read_linked_record_rows_scanned:
  "read_linked_record_rows (scanned_artifact_reading C) H n=finite_linked_record_rows (finite_structure C) H n"
  by (simp only: read_linked_record_rows_def finite_linked_record_rows_def read_linked_rows_scanned)

lemma read_record_candidates_scanned:
  "read_record_candidates (scanned_artifact_reading C) r n=finite_record_body_candidates C r n"
proof -
  have body: "(\<lambda>(ps,xs). read_record_body (scanned_artifact_reading C) r ps xs)=(\<lambda>(ps,xs). finite_record_body C r ps xs)"
    by (simp only: read_record_body_scanned)
  show ?thesis
    by (simp only: read_record_candidates_def finite_record_body_candidates_linked_code body
      read_linked_record_rows_scanned scanned_artifact_reading_fields)
qed

lemma read_payload_leaf_body_scanned:
  "read_payload_leaf_body (scanned_artifact_reading C) a=finite_payload_leaf_body C a"
  by (simp add: fun_eq_iff read_payload_leaf_body_def finite_payload_leaf_body_def read_payload_at_scanned
    scanned_artifact_reading_fields)

lemma read_payload_readings_scanned:
  "read_payload_readings (scanned_artifact_reading C) r=finite_payload_body_readings C r"
  by (simp only: read_payload_readings_def finite_payload_body_readings_def read_payload_leaf_body_scanned
    scanned_artifact_reading_fields)

lemma read_raw_citation_at_scanned:
  "read_raw_citation_at (scanned_artifact_reading C) r c I \<longleftrightarrow> finite_raw_citation_at C r c I"
  by (cases c) (simp_all only: read_raw_citation_at.simps finite_raw_citation_at.simps
    scanned_artifact_reading_fields read_payload_at_scanned)

lemma read_citation_choices_scanned:
  "read_citation_choices (scanned_artifact_reading C) r=finite_citation_choices C r"
  by (simp only: read_citation_choices_def finite_citation_choices_def scanned_artifact_reading_fields)

lemma read_citation_candidates_scanned:
  "read_citation_candidates (scanned_artifact_reading C) r=finite_citation_candidates_formed C r"
proof -
  have raw: "(\<lambda>(c,I). read_raw_citation_at (scanned_artifact_reading C) r c I)=(\<lambda>(c,I). finite_raw_citation_at C r c I)"
    by (simp only: read_raw_citation_at_scanned)
  show ?thesis
    by (simp only: read_citation_candidates_def finite_citation_candidates_formed_def raw
      read_citation_choices_scanned read_empty_on_scanned scanned_artifact_reading_fields)
qed

lemma read_family_body_at_scanned:
  "read_family_body_at (scanned_artifact_reading C) r M \<longleftrightarrow> finite_family_body_at C r M"
  by (simp only: read_family_body_at_def finite_family_body_at_def read_empty_on_scanned scanned_artifact_reading_fields)

lemma read_family_candidates_scanned:
  "read_family_candidates (scanned_artifact_reading C) r=finite_family_body_candidates C r"
  by (simp only: read_family_candidates_def finite_family_body_candidates_def read_family_body_at_scanned
    scanned_artifact_reading_fields)

lemma read_binder_scope_candidates_scanned:
  "read_binder_scope_candidates (scanned_artifact_reading C) b=finite_binder_scope_body_candidates C b"
  by (simp only: read_binder_scope_candidates_def finite_binder_scope_body_candidates_def
    read_family_body_at_scanned scanned_artifact_reading_fields)

lemma read_two_field_record_scanned:
  "read_two_field_record (scanned_artifact_reading C) r F=finite_two_field_record_formed C r F"
  by (simp only: read_two_field_record_def finite_two_field_record_formed_def read_record_candidates_scanned)

lemma read_three_field_record_scanned:
  "read_three_field_record (scanned_artifact_reading C) r F=finite_three_field_record_formed C r F"
  by (simp only: read_three_field_record_def finite_three_field_record_formed_def read_record_candidates_scanned)

lemma read_record_readings_scanned:
  "read_record_readings (scanned_artifact_reading C) r f V reads=finite_record_readings_formed C r f V reads"
  by (simp only: read_record_readings_def finite_record_readings_formed_def read_two_field_record_scanned)

lemma read_variable_readings_scanned:
  "read_variable_readings (scanned_artifact_reading C) V r=finite_variable_readings_formed C V r"
  by (simp only: read_variable_readings_def finite_variable_readings_formed_def read_citation_candidates_scanned)

lemma read_target_readings_scanned:
  "read_target_readings E u (scanned_artifact_reading C) r=finite_target_readings_formed E u C r"
  by (simp only: read_target_readings_def finite_target_readings_formed_def read_citation_candidates_scanned)

section \<open>The readings of one use read the artifacts there through their readings\<close>

text \<open>
  Every syntax reading at a use reads the artifacts there, and every reading it depends on is taken
  at the same use; citations of other uses only locate or quote their targets. The readings of those
  artifacts are therefore taken once, where a reading of the use begins, and passed to every reading
  it depends on. The formed-once readings union over the artifacts at the use, so the readings below
  union over the artifacts' readings in the same way, and they are the formed-once readings for every
  environment.
\<close>

definition artifact_readings_at :: "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> artifact_reading fset" where
  "artifact_readings_at E u=fimage scanned_artifact_reading (finite_artifacts_at E u)"

lemma artifact_readings_at_indexed_code [code]:
  "artifact_readings_at E u=fimage indexed_artifact_reading (finite_artifacts_at E u)"
  by (simp only: artifact_readings_at_def indexed_artifact_reading_function)

lemma artifact_readings_union:
  "ffUnion (fimage F (artifact_readings_at E u))=
    ffUnion (fimage (\<lambda>C. F (scanned_artifact_reading C)) (finite_artifacts_at E u))"
  by (simp add: artifact_readings_at_def fset.map_comp comp_def)

lemma artifact_readings_member:
  "fBex (artifact_readings_at E u) (\<lambda>R. reading_member R a) \<longleftrightarrow>
    fBex (finite_artifacts_at E u) (\<lambda>C. a |\<in>| finite_carrier (finite_structure C))"
  by (auto simp: artifact_readings_at_def scanned_artifact_reading_fields)

fun read_citation_locations ::
  "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> artifact_reading fset \<Rightarrow> citation \<Rightarrow> ('u\<times>local_address) fset" where
  "read_citation_locations E u As (Local a)=(if fBex As (\<lambda>R. reading_member R a) then {|(u,a)|} else {||})"
| "read_citation_locations E u As (External k a)=finite_citation_locations_formed E u (External k a)"
| "read_citation_locations E u As Local_Whole={||}"
| "read_citation_locations E u As (External_Whole k)={||}"

definition read_location_readings where
  "read_location_readings E u As R r=ffUnion (fimage (\<lambda>(c,I).
    fimage (\<lambda>d. (d,I,finite_citation_slots c)) (read_citation_locations E u As c))
      (read_citation_candidates R r))"

fun read_term_readings ::
  "nat \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> artifact_reading fset \<Rightarrow> local_address \<Rightarrow>
    finite_factor_term finite_syntax_reading fset" where
  "read_term_readings 0 E u As r={||}"
| "read_term_readings (Suc n) E u As r=ffUnion (fimage (\<lambda>R.
    read_target_readings E u R r |\<union>| read_payload_readings R r |\<union>|
    read_record_readings R r Finite_Pair {||} (read_term_readings n E u As)) As)"

definition read_pattern_constants where
  "read_pattern_constants E u As V r=ffUnion (fimage (finite_pattern_leaf V) (read_term_readings 1 E u As r))"

fun read_pattern_readings ::
  "nat \<Rightarrow> 'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> artifact_reading fset \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> local_address finite_term_pattern finite_syntax_reading fset" where
  "read_pattern_readings 0 E u As V r={||}"
| "read_pattern_readings (Suc n) E u As V r=read_pattern_constants E u As V r |\<union>|
    ffUnion (fimage (\<lambda>R. read_variable_readings R V r |\<union>|
      read_record_readings R r Finite_Pattern_Pair V (read_pattern_readings n E u As V)) As)"

definition read_sized_pattern_readings where
  "read_sized_pattern_readings E u As V r=ffUnion (fimage (\<lambda>R.
    read_pattern_readings (reading_size R) E u As V r) As)"

definition read_family_readings :: "artifact_reading fset \<Rightarrow> local_address \<Rightarrow> (local_address \<Rightarrow> 'a fset) \<Rightarrow>
    (local_address\<times>'a) fset fset" where
  "read_family_readings As r reads=ffUnion (fimage (\<lambda>R.
    ffUnion (fimage (\<lambda>M. finite_socket_readings M reads) (read_family_candidates R r))) As)"

definition read_call_readings where
  "read_call_readings E u As V r reads=ffUnion (fimage (\<lambda>R. read_two_field_record R r (\<lambda>ps c a.
    finite_join_readings Pair V r ps (read_location_readings E u As R c) (reads a))) As)"

definition read_prospective_call_readings where
  "read_prospective_call_readings E u As V r=read_call_readings E u As V r (read_sized_pattern_readings E u As V)"

fun read_pattern_vector_readings where
  "read_pattern_vector_readings E u As V []={|([],{||},{||})|}"
| "read_pattern_vector_readings E u As V (r#rs)=ffUnion (fimage (\<lambda>(p,J0,W0).
    ffUnion (fimage (\<lambda>(ps,J,W).
      if J0 |\<inter>| J={||} \<and> (J0 |\<union>| J) |\<inter>| (W0 |\<union>| W)={||}
      then {|(p#ps,J0 |\<union>| J,W0 |\<union>| W)|} else {||})
        (read_pattern_vector_readings E u As V rs))) (read_sized_pattern_readings E u As V r))"

definition read_pattern_record_readings where
  "read_pattern_record_readings E u As V r n=ffUnion (fimage (\<lambda>R. ffUnion (fimage (\<lambda>(ports,roots).
    finite_frame_readings V r ports (read_pattern_vector_readings E u As V roots))
      (read_record_candidates R r n))) As)"

definition read_material_readings where
  "read_material_readings E u As V r=ffUnion (fimage (\<lambda>(ps,I,K).
    fimage (\<lambda>M. (M,I,K)) (finite_material_from_fields ps)) (read_pattern_record_readings E u As V r 5))"

definition read_premise_readings where
  "read_premise_readings E u As V r=
    fimage (\<lambda>(c,I,K). (Inl c,I,K)) (read_prospective_call_readings E u As V r) |\<union>|
    fimage (\<lambda>(M,I,K). (Inr M,I,K)) (read_material_readings E u As V r)"

definition read_premise_family_readings where
  "read_premise_family_readings E u As V r=
    fimage (\<lambda>F. (finite_left_sockets F,finite_right_sockets F))
      (read_family_readings As r (\<lambda>a. finite_reading_values (read_premise_readings E u As V a)))"

definition read_schema_body_readings where
  "read_schema_body_readings E u As R r ps b c m =
    ffUnion (fimage (\<lambda>V. ffUnion (fimage (\<lambda>(p,I,K).
      ffUnion (fimage (\<lambda>(Q,M).
        let S=\<lparr>finite_schema_conclusion=p,finite_schema_premises=Q,finite_schema_materials=M\<rparr> in
        if V=finite_schema_variables S \<and>
          finsert r (fset_of_list ps) |\<inter>| (finsert b V |\<union>| I |\<union>| {|m|})={||} \<and>
          finsert b V |\<inter>| I={||} \<and> b\<noteq>m \<and> m |\<notin>| I
        then {|S|} else {||}) (read_premise_family_readings E u As V m)))
      (read_sized_pattern_readings E u As V c))) (read_binder_scope_candidates R b))"

definition read_schema_readings where
  "read_schema_readings E u As r=ffUnion (fimage (\<lambda>R.
    read_three_field_record R r (read_schema_body_readings E u As R r)) As)"

definition read_scoped_record where
  "read_scoped_record E u As R r ps b q=ffUnion (fimage (\<lambda>V.
    ffilter (\<lambda>(p,I,K). finite_pattern_variables p=V)
      (finite_join_readings (\<lambda>(_::unit) p. p) {||} r ps {|((),finsert b V,{||})|}
        (read_sized_pattern_readings E u As V q))) (read_binder_scope_candidates R b))"

definition read_scoped_pattern_readings where
  "read_scoped_pattern_readings E u As r=ffUnion (fimage (\<lambda>R.
    read_two_field_record R r (read_scoped_record E u As R r)) As)"

definition read_definition_body_readings where
  "read_definition_body_readings E u As r ps i m =
    ffUnion (fimage (\<lambda>(p,I,K).
      if finsert r (fset_of_list ps) |\<inter>| (I |\<union>| {|m|})={||} \<and> m |\<notin>| I
      then fimage (Pair p) (read_family_readings As m (read_schema_readings E u As)) else {||})
        (read_scoped_pattern_readings E u As i))"

definition read_definition_readings where
  "read_definition_readings E u As r=ffUnion (fimage (\<lambda>R.
    read_two_field_record R r (read_definition_body_readings E u As r)) As)"

section \<open>Taken at the artifacts of the use, every reading is the formed-once one\<close>

lemma read_citation_locations_at:
  "read_citation_locations E u (artifact_readings_at E u) c=finite_citation_locations_formed E u c"
  by (cases c) (simp_all only: read_citation_locations.simps finite_citation_locations_formed.simps
    artifact_readings_member)

lemma read_location_readings_at:
  "read_location_readings E u (artifact_readings_at E u) (scanned_artifact_reading C) r=
    finite_location_readings_formed E u C r"
proof -
  have locations: "read_citation_locations E u (artifact_readings_at E u)=finite_citation_locations_formed E u"
    by (rule ext) (rule read_citation_locations_at)
  show ?thesis
    by (simp only: read_location_readings_def finite_location_readings_formed_def locations
      read_citation_candidates_scanned)
qed

lemma read_term_readings_at:
  "read_term_readings n E u (artifact_readings_at E u)=finite_term_readings_formed n E u"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  show ?case
    by (rule ext) (simp only: read_term_readings.simps(2) finite_term_readings_formed.simps(2) Suc.IH
      artifact_readings_union read_target_readings_scanned read_payload_readings_scanned
      read_record_readings_scanned)
qed

lemma read_pattern_constants_at:
  "read_pattern_constants E u (artifact_readings_at E u) V r=finite_pattern_constants_formed E u V r"
  by (simp only: read_pattern_constants_def finite_pattern_constants_formed_def read_term_readings_at)

lemma read_pattern_readings_at:
  "read_pattern_readings n E u (artifact_readings_at E u) V=finite_pattern_readings_formed n E u V"
proof (induction n)
  case 0
  show ?case by (rule ext) simp
next
  case (Suc n)
  show ?case
    by (rule ext) (simp only: read_pattern_readings.simps(2) finite_pattern_readings_formed.simps(2) Suc.IH
      read_pattern_constants_at artifact_readings_union read_variable_readings_scanned read_record_readings_scanned)
qed

lemma read_sized_pattern_readings_at:
  "read_sized_pattern_readings E u (artifact_readings_at E u) V=finite_pattern_readings_carrier_formed E u V"
  by (rule ext) (simp only: read_sized_pattern_readings_def finite_pattern_readings_carrier_formed_def
    read_pattern_readings_at artifact_readings_union scanned_artifact_reading_fields)

lemma read_family_readings_at:
  "read_family_readings (artifact_readings_at E u) r reads=finite_family_readings_formed E u r reads"
  by (simp only: read_family_readings_def finite_family_readings_formed_def artifact_readings_union
    read_family_candidates_scanned)

lemma read_call_readings_at:
  "read_call_readings E u (artifact_readings_at E u) V r reads=finite_call_readings_formed E u V r reads"
  by (simp only: read_call_readings_def finite_call_readings_formed_def artifact_readings_union
    read_two_field_record_scanned read_location_readings_at)

lemma read_prospective_call_readings_at:
  "read_prospective_call_readings E u (artifact_readings_at E u) V r=
    finite_prospective_call_readings_formed E u V r"
  by (simp only: read_prospective_call_readings_def finite_prospective_call_readings_formed_def
    read_sized_pattern_readings_at read_call_readings_at)

lemma read_pattern_vector_readings_at:
  "read_pattern_vector_readings E u (artifact_readings_at E u) V rs=finite_pattern_vector_readings_formed E u V rs"
  by (induction rs) (simp_all only: read_pattern_vector_readings.simps finite_pattern_vector_readings_formed.simps
    read_sized_pattern_readings_at)

lemma read_pattern_record_readings_at:
  "read_pattern_record_readings E u (artifact_readings_at E u) V r n=finite_pattern_record_readings_formed E u V r n"
proof -
  have vectors: "read_pattern_vector_readings E u (artifact_readings_at E u) V=finite_pattern_vector_readings_formed E u V"
    by (rule ext) (rule read_pattern_vector_readings_at)
  show ?thesis
    by (simp only: read_pattern_record_readings_def finite_pattern_record_readings_formed_def vectors
      artifact_readings_union read_record_candidates_scanned)
qed

lemma read_material_readings_at:
  "read_material_readings E u (artifact_readings_at E u) V r=finite_native_material_readings_formed E u V r"
  by (simp only: read_material_readings_def finite_native_material_readings_formed_def read_pattern_record_readings_at)

lemma read_premise_readings_at:
  "read_premise_readings E u (artifact_readings_at E u) V=finite_native_premise_readings_formed E u V"
  by (rule ext) (simp only: read_premise_readings_def finite_native_premise_readings_formed_def
    read_prospective_call_readings_at read_material_readings_at)

lemma read_premise_family_readings_at:
  "read_premise_family_readings E u (artifact_readings_at E u) V r=
    finite_native_premise_family_readings_formed E u V r"
  by (simp only: read_premise_family_readings_def finite_native_premise_family_readings_formed_def
    read_premise_readings_at read_family_readings_at)

lemma read_schema_body_readings_at:
  "read_schema_body_readings E u (artifact_readings_at E u) (scanned_artifact_reading C) r=
    finite_schema_body_readings_formed E u C r"
proof -
  have families: "read_premise_family_readings E u (artifact_readings_at E u)=
      finite_native_premise_family_readings_formed E u"
    by (intro ext) (rule read_premise_family_readings_at)
  have patterns: "read_sized_pattern_readings E u (artifact_readings_at E u)=finite_pattern_readings_carrier_formed E u"
    by (intro ext) (rule fun_cong[OF read_sized_pattern_readings_at])
  show ?thesis
    by (intro ext) (simp only: read_schema_body_readings_def finite_schema_body_readings_formed_def families patterns
      read_binder_scope_candidates_scanned)
qed

lemma read_schema_readings_at:
  "read_schema_readings E u (artifact_readings_at E u) r=finite_native_schema_readings_formed E u r"
  by (simp only: read_schema_readings_def finite_native_schema_readings_formed_def artifact_readings_union
    read_three_field_record_scanned read_schema_body_readings_at)

lemma read_scoped_record_at:
  "read_scoped_record E u (artifact_readings_at E u) (scanned_artifact_reading C) r=finite_scoped_record_formed E u C r"
proof -
  have patterns: "read_sized_pattern_readings E u (artifact_readings_at E u)=finite_pattern_readings_carrier_formed E u"
    by (intro ext) (rule fun_cong[OF read_sized_pattern_readings_at])
  show ?thesis
    by (intro ext) (simp only: read_scoped_record_def finite_scoped_record_formed_def patterns
      read_binder_scope_candidates_scanned)
qed

lemma read_scoped_pattern_readings_at:
  "read_scoped_pattern_readings E u (artifact_readings_at E u) r=finite_scoped_pattern_readings_formed E u r"
  by (simp only: read_scoped_pattern_readings_def finite_scoped_pattern_readings_formed_def artifact_readings_union
    read_two_field_record_scanned read_scoped_record_at)

lemma read_definition_body_readings_at:
  "read_definition_body_readings E u (artifact_readings_at E u) r ps i m=finite_definition_body_readings_formed E u r ps i m"
proof -
  have schemas: "read_schema_readings E u (artifact_readings_at E u)=finite_native_schema_readings_formed E u"
    by (rule ext) (rule read_schema_readings_at)
  show ?thesis
    by (simp only: read_definition_body_readings_def finite_definition_body_readings_formed_def schemas
      read_family_readings_at read_scoped_pattern_readings_at)
qed

lemma read_definition_readings_at:
  "read_definition_readings E u (artifact_readings_at E u) r=finite_native_definition_readings_formed E u r"
proof -
  have body: "read_definition_body_readings E u (artifact_readings_at E u) r=finite_definition_body_readings_formed E u r"
    by (intro ext) (rule read_definition_body_readings_at)
  show ?thesis
    by (simp only: read_definition_readings_def finite_native_definition_readings_formed_def body
      artifact_readings_union read_two_field_record_scanned)
qed

section \<open>Every formed-once reading takes the readings of its artifacts once\<close>

text \<open>
  The formed-once readings are the code of every guarded entry (the definition, schema, scoped
  pattern, family, call, record and vector readings and the bounded term and pattern readings, each
  guarded by one formation check, and package formation, sites and graph through the site reading).
  Their own code now takes the readings of the artifacts at the use where a reading begins; the
  guarded entries and their code equations are unchanged.
\<close>

declare finite_term_readings_formed.simps[code del] finite_pattern_readings_formed.simps[code del]
  finite_pattern_vector_readings_formed.simps[code del]

lemma finite_term_readings_formed_read_code [code]:
  "finite_term_readings_formed n E u r=read_term_readings n E u (artifact_readings_at E u) r"
  by (simp only: read_term_readings_at)

lemma finite_pattern_constants_formed_read_code [code]:
  "finite_pattern_constants_formed E u V r=read_pattern_constants E u (artifact_readings_at E u) V r"
  by (simp only: read_pattern_constants_at)

lemma finite_pattern_readings_formed_read_code [code]:
  "finite_pattern_readings_formed n E u V r=read_pattern_readings n E u (artifact_readings_at E u) V r"
  by (simp only: read_pattern_readings_at)

lemma finite_pattern_readings_carrier_formed_read_code [code]:
  "finite_pattern_readings_carrier_formed E u V r=read_sized_pattern_readings E u (artifact_readings_at E u) V r"
  by (simp only: read_sized_pattern_readings_at)

lemma finite_family_readings_formed_read_code [code]:
  "finite_family_readings_formed E u r reads=read_family_readings (artifact_readings_at E u) r reads"
  by (simp only: read_family_readings_at)

lemma finite_call_readings_formed_read_code [code]:
  "finite_call_readings_formed E u V r reads=read_call_readings E u (artifact_readings_at E u) V r reads"
  by (simp only: read_call_readings_at)

lemma finite_prospective_call_readings_formed_read_code [code]:
  "finite_prospective_call_readings_formed E u V r=read_prospective_call_readings E u (artifact_readings_at E u) V r"
  by (simp only: read_prospective_call_readings_at)

lemma finite_pattern_vector_readings_formed_read_code [code]:
  "finite_pattern_vector_readings_formed E u V rs=read_pattern_vector_readings E u (artifact_readings_at E u) V rs"
  by (simp only: read_pattern_vector_readings_at)

lemma finite_pattern_record_readings_formed_read_code [code]:
  "finite_pattern_record_readings_formed E u V r n=read_pattern_record_readings E u (artifact_readings_at E u) V r n"
  by (simp only: read_pattern_record_readings_at)

lemma finite_native_material_readings_formed_read_code [code]:
  "finite_native_material_readings_formed E u V r=read_material_readings E u (artifact_readings_at E u) V r"
  by (simp only: read_material_readings_at)

lemma finite_native_premise_readings_formed_read_code [code]:
  "finite_native_premise_readings_formed E u V r=read_premise_readings E u (artifact_readings_at E u) V r"
  by (simp only: read_premise_readings_at)

lemma finite_native_premise_family_readings_formed_read_code [code]:
  "finite_native_premise_family_readings_formed E u V r=read_premise_family_readings E u (artifact_readings_at E u) V r"
  by (simp only: read_premise_family_readings_at)

lemma finite_native_schema_readings_formed_read_code [code]:
  "finite_native_schema_readings_formed E u r=read_schema_readings E u (artifact_readings_at E u) r"
  by (simp only: read_schema_readings_at)

lemma finite_scoped_pattern_readings_formed_read_code [code]:
  "finite_scoped_pattern_readings_formed E u r=read_scoped_pattern_readings E u (artifact_readings_at E u) r"
  by (simp only: read_scoped_pattern_readings_at)

lemma finite_native_definition_readings_formed_read_code [code]:
  "finite_native_definition_readings_formed E u r=read_definition_readings E u (artifact_readings_at E u) r"
  by (simp only: read_definition_readings_at)

text \<open>
  The results are the original readings for every environment: the scanned reading states the
  questions, the indexed reading answers them through the indexes the complete data walk reads
  through, and the two readings are equal. The guarded entries, which the seeded development state
  expands as its formation roots, keep their code equations; only the readings they guard, which
  that state leaves on its frontier, are computed differently.
\<close>

end
