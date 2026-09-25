theory Factor_Additions_Counterparts
  imports Factor_Package_Additions Factor_Inclusion_Admission_Counterparts Factor_Finite_Coordinate_Value_Readers
    RRA_Finite_Environment_Positions Finite_Keyed_Table_Comparison Factor_Finite_Equality_Source
begin

text \<open>
  The additions notion's counterpart and its instance at the callee boundary (DECISIONS.md "The native evaluator
  evaluates above an implemented base: the given's readers enter through counterparts exact to their native
  definitions", build C2). A counterpart is a function on finite terms exact at every term to its reader's result
  relation: it reads the argument back through the finite readers, each exact to its notion, and decides on what
  it read the relation the reader's own contract states. The native definitions stay normative: a counterpart's
  exactness is its proof, proved from the finite readers' exactness and the reader's contract, neither re-proved.
\<close>

section \<open>A site value, and a pair of them, read back\<close>

lemma decode_finite_pair_iff:
  "decode_finite_term t=Pair_Term x y \<longleftrightarrow>
    (\<exists>a b. t=Finite_Pair a b \<and> decode_finite_term a=x \<and> decode_finite_term b=y)"
  by (cases t) auto

text \<open>
  A site value is read by the site-value reader of @{text Factor_Inclusion_Admission_Counterparts}
  (@{const finite_site_read}); a pair of them is read componentwise.
\<close>

abbreviation finite_site_pair_read :: "finite_factor_term \<Rightarrow>
    ((local_address option finite_artifact_environment\<times>local_address option\<times>local_address)\<times>
      (local_address option finite_artifact_environment\<times>local_address option\<times>local_address)) option" where
  "finite_site_pair_read \<equiv> finite_pair_read finite_site_read finite_site_read"

theorem finite_site_pair_read_exact:
  "finite_site_pair_read z=Some ((E,u,r),(F,v,s)) \<longleftrightarrow> (\<exists>t w. decode_finite_term z=Pair_Term t w \<and>
    site_value_presents (decode_finite_environment E) u r t \<and> site_value_presents (decode_finite_environment F) v s w)"
proof -
  have site: "finite_site_read a=Some x \<longleftrightarrow>
      site_value_presents (decode_finite_environment (fst x)) (fst (snd x)) (snd (snd x)) (decode_finite_term a)" for a x
    by (cases x) (simp only: finite_site_read_exact fst_conv snd_conv split_pairs)
  show ?thesis
    using finite_pair_read_present[where
      P="\<lambda>x p. site_value_presents (decode_finite_environment (fst x)) (fst (snd x)) (snd (snd x)) p"
      and Q="\<lambda>x p. site_value_presents (decode_finite_environment (fst x)) (fst (snd x)) (snd (snd x)) p",
      OF site site, of z "(E,u,r)" "(F,v,s)"]
    by simp
qed

section \<open>The additions counterpart, stated once for every callee\<close>

text \<open>
  On a pair of site values the counterpart reads the candidate's package (@{const finite_native_source}) and
  holds when it is read and each of its definitions is a definition of the given's package or the callee's
  counterpart holds of the whole pair beside the definition's site value; on every other term it is false. It
  is exact to @{const package_additions_result} at a callee predicate whenever the callee's counterpart is exact
  to that predicate, as @{locale package_additions_profile} states the native entry for every callee.
\<close>

definition finite_package_additions :: "(finite_factor_term \<Rightarrow> bool) \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_package_additions callee z=(case finite_site_pair_read z of None \<Rightarrow> False
    | Some ((E,u,r),(F,v,s)) \<Rightarrow> (case finite_native_source F v s of None \<Rightarrow> False
      | Some R \<Rightarrow> (let given=finite_native_source E u r in fBall (finite_system_definitions R) (\<lambda>d.
          (case given of None \<Rightarrow> False | Some Q \<Rightarrow> d |\<in>| finite_system_definitions Q) \<or>
          callee (Finite_Pair z (finite_site_data d))))))"

lemma finite_given_member:
  "(case finite_native_source E u r of None \<Rightarrow> False | Some Q \<Rightarrow> d |\<in>| finite_system_definitions Q) \<longleftrightarrow>
    (\<exists>Q. native_package_at (decode_finite_environment E) u r Q \<and> d\<in>system_definitions Q)"
proof (cases "finite_native_source E u r")
  case None
  then show ?thesis using finite_native_source_absent[of E u r] by auto
next
  case (Some Q)
  have package: "native_package_at (decode_finite_environment E) u r (decode_finite_system Q)"
    using Some by (simp add: finite_native_source_correct)
  show ?thesis using Some package
    by (auto simp: finite_system_definitions_correct dest: native_package_unique[OF package])
qed

theorem finite_package_additions_exact:
  assumes callee: "\<And>x. c x \<longleftrightarrow> C (decode_finite_term x)"
  shows "finite_package_additions c z \<longleftrightarrow> package_additions_result C (decode_finite_term z)"
proof
  assume holds: "finite_package_additions c z"
  obtain E u r F v s where read: "finite_site_pair_read z=Some ((E,u,r),(F,v,s))"
    using holds by (cases "finite_site_pair_read z") (auto simp: finite_package_additions_def split: prod.splits)
  obtain R where source: "finite_native_source F v s=Some R"
    using holds read by (cases "finite_native_source F v s") (auto simp: finite_package_additions_def)
  have members: "fBall (finite_system_definitions R) (\<lambda>d.
      (case finite_native_source E u r of None \<Rightarrow> False | Some Q \<Rightarrow> d |\<in>| finite_system_definitions Q) \<or>
      c (Finite_Pair z (finite_site_data d)))"
    using holds read source by (simp add: finite_package_additions_def Let_def)
  obtain t w where parts: "decode_finite_term z=Pair_Term t w"
      "site_value_presents (decode_finite_environment E) u r t" "site_value_presents (decode_finite_environment F) v s w"
    using read by (auto simp: finite_site_pair_read_exact)
  have package: "native_package_at (decode_finite_environment F) v s (decode_finite_system R)"
    using source by (simp add: finite_native_source_correct)
  have all: "\<forall>d\<in>system_definitions (decode_finite_system R).
      (\<exists>Q. native_package_at (decode_finite_environment E) u r Q \<and> d\<in>system_definitions Q) \<or>
      C (Pair_Term (Pair_Term t w) (definition_site_value d))"
  proof
    fix d assume "d\<in>system_definitions (decode_finite_system R)"
    then have "d |\<in>| finite_system_definitions R" by (simp add: finite_system_definitions_correct)
    then have "(case finite_native_source E u r of None \<Rightarrow> False | Some Q \<Rightarrow> d |\<in>| finite_system_definitions Q) \<or>
      c (Finite_Pair z (finite_site_data d))" by (rule fbspec[OF members])
    then show "(\<exists>Q. native_package_at (decode_finite_environment E) u r Q \<and> d\<in>system_definitions Q) \<or>
      C (Pair_Term (Pair_Term t w) (definition_site_value d))"
      by (simp add: finite_given_member callee parts(1))
  qed
  show "package_additions_result C (decode_finite_term z)"
    using parts package all by blast
next
  assume "package_additions_result C (decode_finite_term z)"
  then obtain E u r t F v s w R where parts: "decode_finite_term z=Pair_Term t w" "site_value_presents E u r t"
      "site_value_presents F v s w" "native_package_at F v s R"
    and members: "\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      C (Pair_Term (Pair_Term t w) (definition_site_value d))" by blast
  have left: "decode_finite_environment (finite_environment_of E)=E"
    using site_value_presents_formed[OF parts(2)] by (simp add: decode_finite_environment_of)
  have right: "decode_finite_environment (finite_environment_of F)=F"
    using site_value_presents_formed[OF parts(3)] by (simp add: decode_finite_environment_of)
  have read: "finite_site_pair_read z=Some ((finite_environment_of E,u,r),(finite_environment_of F,v,s))"
    using parts(1-3) left right by (auto simp only: finite_site_pair_read_exact)
  obtain R' where source: "finite_native_source (finite_environment_of F) v s=Some R'"
    using parts(4) right finite_native_source_absent[of "finite_environment_of F" v s]
    by (cases "finite_native_source (finite_environment_of F) v s") auto
  have "native_package_at F v s (decode_finite_system R')"
    using source right by (simp add: finite_native_source_correct)
  then have same: "decode_finite_system R'=R" by (rule native_package_unique[OF _ parts(4)])
  have "fBall (finite_system_definitions R') (\<lambda>d.
      (case finite_native_source (finite_environment_of E) u r of None \<Rightarrow> False
        | Some Q \<Rightarrow> d |\<in>| finite_system_definitions Q) \<or>
      c (Finite_Pair z (finite_site_data d)))"
  proof (rule fBallI)
    fix d assume "d |\<in>| finite_system_definitions R'"
    then have "d\<in>system_definitions R" using same by (simp add: finite_system_definitions_correct)
    then have "(\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      C (Pair_Term (Pair_Term t w) (definition_site_value d))" using members by blast
    then show "(case finite_native_source (finite_environment_of E) u r of None \<Rightarrow> False
        | Some Q \<Rightarrow> d |\<in>| finite_system_definitions Q) \<or> c (Finite_Pair z (finite_site_data d))"
      using left parts(1) by (simp add: finite_given_member callee)
  qed
  then show "finite_package_additions c z"
    using read source by (simp add: finite_package_additions_def Let_def)
qed

section \<open>The callee boundary's callee: absence of the member's use from the given's artifact rows\<close>

text \<open>
  The counterpart of 393 reads the shape @{thm [source] use_absence_exact} states: the given's artifact rows,
  their keys, and the member's key beside the rest of the pair. Each part is read by the identity reader, the
  rows as a sequence of pairs (@{const finite_sequence_read}); the key's self-containment is decided by
  @{const finite_data_projection} and the rows' formation by @{const finite_keyed_rows_formed}. The keys are
  compared as finite terms, which the decoding identifies with the self-contained data the native relation
  compares (key absence at 20 over 3).
\<close>

lemma finite_term_reads: "finite_reads Some id"
  by (rule finite_readsI) simp

lemma decode_finite_pair_rows:
  "decode_finite_term (finite_sequence_presentation (finite_pair_presentation id id) ys)=
    pair_list_term (decoded_keyed_rows ys)"
  by (induction ys) (auto simp: finite_pair_presentation_def)

lemma finite_pair_rows_complete:
  "map decode_finite_term xs=map (\<lambda>(k,v). Pair_Term k v) zs \<Longrightarrow>
    \<exists>ys. xs=map (finite_pair_presentation id id) ys \<and> decoded_keyed_rows ys=zs"
proof (induction xs arbitrary: zs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain z zs' where zs: "zs=z#zs'" using Cons.prems by (cases zs) auto
  obtain k v where z: "z=(k,v)" by (cases z)
  have head: "decode_finite_term x=Pair_Term k v"
    and tail: "map decode_finite_term xs=map (\<lambda>(k,v). Pair_Term k v) zs'" using Cons.prems zs z by simp_all
  obtain a b where x: "x=Finite_Pair a b" "decode_finite_term a=k" "decode_finite_term b=v"
    using head by (auto simp: decode_finite_pair_iff)
  obtain ys where rows: "xs=map (finite_pair_presentation id id) ys" "decoded_keyed_rows ys=zs'"
    using Cons.IH[OF tail] by blast
  show ?case by (rule exI[of _ "(a,b)#ys"]) (use rows x zs z in \<open>simp add: finite_pair_presentation_def\<close>)
qed

lemma finite_key_rows_reads:
  "finite_sequence_read (finite_pair_read Some Some) a=Some ys \<longleftrightarrow>
    a=finite_sequence_presentation (finite_pair_presentation id id) ys"
  by (rule finite_readsD[OF finite_sequence_reads[OF finite_pair_reads[OF finite_term_reads finite_term_reads]]])

lemma finite_key_rows_read_complete:
  assumes source: "decode_finite_term a=pair_list_term zs"
  shows "\<exists>ys. finite_sequence_read (finite_pair_read Some Some) a=Some ys \<and> decoded_keyed_rows ys=zs"
proof -
  obtain xs where list: "finite_data_list_read a=Some xs" "map decode_finite_term xs=map (\<lambda>(k,v). Pair_Term k v) zs"
    by (rule finite_data_list_read_complete[OF source])
  obtain ys where rows: "xs=map (finite_pair_presentation id id) ys" "decoded_keyed_rows ys=zs"
    using finite_pair_rows_complete[OF list(2)] by blast
  have "decode_finite_term a=decode_finite_term (finite_sequence_presentation (finite_pair_presentation id id) ys)"
    by (simp only: source decode_finite_pair_rows rows(2))
  then show ?thesis using rows(2) by (simp only: decode_finite_term_injective finite_key_rows_reads) blast
qed

definition finite_absence_parts :: "finite_factor_term \<Rightarrow>
    ((((finite_factor_term\<times>finite_factor_term)\<times>finite_factor_term)\<times>finite_factor_term)\<times>
      (finite_factor_term\<times>finite_factor_term)) option" where
  "finite_absence_parts=finite_pair_read (finite_pair_read (finite_pair_read (finite_pair_read Some Some) Some) Some)
    (finite_pair_read Some Some)"

lemma finite_absence_parts_result:
  "finite_absence_parts t=Some ((((a,b),c),y),(k,q)) \<longleftrightarrow>
    t=Finite_Pair (Finite_Pair (Finite_Pair (Finite_Pair a b) c) y) (Finite_Pair k q)"
proof -
  have "finite_reads finite_absence_parts (finite_pair_presentation (finite_pair_presentation
      (finite_pair_presentation (finite_pair_presentation id id) id) id) (finite_pair_presentation id id))"
    unfolding finite_absence_parts_def by (intro finite_pair_reads finite_term_reads)
  then show ?thesis by (simp add: finite_readsD finite_pair_presentation_def)
qed

lemma finite_absence_parts_at:
  "finite_absence_parts (Finite_Pair (Finite_Pair (Finite_Pair (Finite_Pair a b) c) y) (Finite_Pair k q))=
    Some ((((a,b),c),y),(k,q))"
  by (simp only: finite_absence_parts_result)

definition finite_use_absence :: "finite_factor_term \<Rightarrow> bool" where
  "finite_use_absence t=(case finite_absence_parts t of None \<Rightarrow> False
    | Some ((((a,b),c),y),(k,q)) \<Rightarrow> (case finite_sequence_read (finite_pair_read Some Some) a of None \<Rightarrow> False
      | Some ys \<Rightarrow> finite_term_formed b \<and> finite_term_formed c \<and> finite_term_formed y \<and> finite_term_formed q \<and>
          finite_term_formed k \<and> finite_data_projection k=Some k \<and> finite_keyed_rows_formed ys \<and>
          k\<notin>set (map fst ys)))"

theorem finite_use_absence_exact:
  "finite_use_absence t \<longleftrightarrow> (393,decode_finite_term t)\<in>positive_meaning use_additions_system"
proof -
  have keys: "decode_finite_term k\<notin>set (map fst (decoded_keyed_rows ys)) \<longleftrightarrow> k\<notin>set (map fst ys)" for k ys
    by (induction ys) auto
  show ?thesis
  proof
    assume "finite_use_absence t"
    then obtain a b c y k q ys where parts: "finite_absence_parts t=Some ((((a,b),c),y),(k,q))"
        "finite_sequence_read (finite_pair_read Some Some) a=Some ys"
      and formed: "finite_term_formed b" "finite_term_formed c" "finite_term_formed y" "finite_term_formed q"
        "finite_term_formed k" "finite_data_projection k=Some k"
      and table: "finite_keyed_rows_formed ys" "k\<notin>set (map fst ys)"
      by (auto simp: finite_use_absence_def split: option.splits prod.splits)
    have shape: "decode_finite_term t=Pair_Term (Pair_Term (Pair_Term (Pair_Term
        (pair_list_term (decoded_keyed_rows ys)) (decode_finite_term b))
        (decode_finite_term c)) (decode_finite_term y)) (Pair_Term (decode_finite_term k) (decode_finite_term q))"
      using parts by (simp add: finite_absence_parts_result finite_key_rows_reads decode_finite_pair_rows)
    have krows: "formed_key_rows (decoded_keyed_rows ys)" using table(1) by (simp only: finite_keyed_rows_formed_correct)
    have kabs: "decode_finite_term k\<notin>set (map fst (decoded_keyed_rows ys))" using table(2) keys by blast
    show "(393,decode_finite_term t)\<in>positive_meaning use_additions_system" unfolding use_absence_exact
      by (rule exI[of _ "decoded_keyed_rows ys"], rule exI[of _ "decode_finite_term b"],
        rule exI[of _ "decode_finite_term c"], rule exI[of _ "decode_finite_term y"],
        rule exI[of _ "decode_finite_term k"], rule exI[of _ "decode_finite_term q"])
        (use shape krows kabs formed in \<open>simp add: finite_term_formed_correct\<close>)
  next
    assume "(393,decode_finite_term t)\<in>positive_meaning use_additions_system"
    then obtain xs b c y k q where source: "decode_finite_term t=Pair_Term (Pair_Term (Pair_Term (Pair_Term
        (pair_list_term xs) b) c) y) (Pair_Term k q)"
      and formed: "term_formed b" "term_formed c" "term_formed y" "term_formed q" "term_formed k" "self_contained_term k"
      and table: "formed_key_rows xs" "k\<notin>set (map fst xs)"
      unfolding use_absence_exact by blast
    obtain a' b' c' y' k' q' where shape: "t=Finite_Pair (Finite_Pair (Finite_Pair (Finite_Pair a' b') c') y') (Finite_Pair k' q')"
      and parts: "decode_finite_term a'=pair_list_term xs" "decode_finite_term b'=b" "decode_finite_term c'=c"
        "decode_finite_term y'=y" "decode_finite_term k'=k" "decode_finite_term q'=q"
      using source by (auto simp: decode_finite_pair_iff)
    obtain ys where read: "finite_sequence_read (finite_pair_read Some Some) a'=Some ys"
        and same: "decoded_keyed_rows ys=xs"
      using finite_key_rows_read_complete[OF parts(1)] by blast
    have frows: "finite_keyed_rows_formed ys" using table(1) same by (simp only: finite_keyed_rows_formed_correct)
    have fkey: "k'\<notin>set (map fst ys)" using keys[of k' ys] table(2) same parts(5) by simp
    have fterms: "finite_term_formed b'" "finite_term_formed c'" "finite_term_formed y'" "finite_term_formed q'"
        "finite_term_formed k'" "finite_data_projection k'=Some k'"
      using formed parts by (simp_all add: finite_term_formed_correct)
    show "finite_use_absence t"
      using frows fkey fterms by (simp add: finite_use_absence_def shape finite_absence_parts_at read)
  qed
qed

section \<open>The callee boundary: the additions counterpart at the use absence\<close>

definition finite_use_additions :: "finite_factor_term \<Rightarrow> bool" where
  "finite_use_additions=finite_package_additions finite_use_absence"

theorem finite_use_additions_exact:
  "finite_use_additions z \<longleftrightarrow> (392,decode_finite_term z)\<in>positive_meaning use_additions_system"
  using finite_package_additions_exact[where C="\<lambda>t. (393,t)\<in>positive_meaning use_additions_system",
    OF finite_use_absence_exact, of z]
  by (simp only: finite_use_additions_def use_additions.exact)

corollary finite_use_additions_on_values:
  assumes first: "site_value_presents E u r (decode_finite_term a)"
    and second: "site_value_presents F v s (decode_finite_term b)"
  shows "finite_use_additions (Finite_Pair a b) \<longleftrightarrow> (\<exists>R. native_package_at F v s R \<and>
    (\<forall>d\<in>system_definitions R. (\<exists>Q. native_package_at E u r Q \<and> d\<in>system_definitions Q) \<or>
      fst d\<notin>environment_uses E))"
  by (simp only: finite_use_additions_exact decode_finite_term.simps use_additions_on_values[OF first second])

text \<open>
  The counterpart of 393 compares uses as values where the native relation compares them as self-contained data;
  the relation's use-equivariance (@{thm [source] use_key_absence_equivariant}) holds of the relation the
  counterpart computes, being a clause of that relation, and is not proved again.
\<close>

section \<open>Controls\<close>

text \<open>
  The equality program's artifact placed at a use; its package at address [0] holds one definition, at the same
  use and address [1]. A one-atom artifact at the use None holds a position and no definition of that package.
\<close>

definition additions_control_environment :: "local_address option \<Rightarrow> local_address option finite_artifact_environment" where
  "additions_control_environment u=finite_enumerated_environment [(u,finite_equality_artifact)] []"

definition control_atom_environment :: "local_address option finite_artifact_environment" where
  "control_atom_environment=finite_enumerated_environment [(None,finite_enumerated_artifact [[0]] [] [] [])] []"


definition control_absence :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "control_absence k=Finite_Pair (Finite_Pair (Finite_Pair (Finite_Pair
    (finite_data_list [Finite_Pair (finite_use_data None) (Finite_Payload [])]) (Finite_Payload []))
    (Finite_Payload [])) (Finite_Payload [])) (Finite_Pair k (Finite_Payload []))"

text \<open>
  Each control's outcome beside its label: the reader at a site value and at a site outside its environment's
  positions (whether a reading is returned); 393 at a key among the rows and at one absent from them; 392 at a
  pair whose second package holds only the first's definitions, at one adding a definition at a use the first's
  environment does not hold, and at one adding a definition at a use it holds.
\<close>

value "[(''reader: site value read'', finite_site_read (finite_site_presented (additions_control_environment None) None [0])\<noteq>None),
  (''reader: site outside the positions read'',
    finite_site_read (finite_site_presented (additions_control_environment None) None [99])\<noteq>None),
  (''393: key among the rows'', finite_use_absence (control_absence (finite_use_data None))),
  (''393: key absent from the rows'', finite_use_absence (control_absence (finite_use_data (Some [0])))),
  (''392: the given definitions only'', finite_use_additions (Finite_Pair
    (finite_site_presented (additions_control_environment None) None [0]) (finite_site_presented (additions_control_environment None) None [0]))),
  (''392: added at a use the first does not hold'', finite_use_additions (Finite_Pair
    (finite_site_presented (additions_control_environment (Some [0])) (Some [0]) [0])
    (finite_site_presented (additions_control_environment None) None [0]))),
  (''392: added at a use the first holds'', finite_use_additions (Finite_Pair
    (finite_site_presented control_atom_environment None [0]) (finite_site_presented (additions_control_environment None) None [0])))]"

end
