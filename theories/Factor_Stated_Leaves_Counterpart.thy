theory Factor_Stated_Leaves_Counterpart
  imports Factor_Stated_Leaves Factor_Audit_Counterparts Factor_Finite_Ground_Source "HOL-Library.List_Lexorder"
begin

text \<open>
  The counterpart of the stated-leaves reader, entry 590 of @{const stated_report_system} (DECISIONS.md "The
  native evaluator evaluates above an implemented base: the given's readers enter through counterparts exact
  to their native definitions", decision 5). On a term that is a source-root argument beside a report it reads
  the argument by the source-root reader (@{thm [source] finite_source_root_read_exact}), the definition at the
  argument's site by @{const finite_native_definition_readings}, and the report by a reader accepting every
  enumeration of its rows; it computes the definition's report by @{const finite_definition_stated} and
  compares. Every other term it refuses. It is exact at every finite term to the reader's result relation, and
  so to 590's positive meaning by @{thm [source] stated_report_exact}. The native definition stays normative:
  the exactness is the proof, from the readers' exactness, @{thm [source] finite_native_definition_readings_correct}
  and @{thm [source] finite_definition_stated_exact}, none proved again.
\<close>

section \<open>What the report states of targets and ground clauses\<close>

text \<open>
  For the criticism that classifies a report (task 381, (h)): the targets reported at a clause's places are
  exactly the target leaves of the clause, and with the interface's those of the definition; and a clause
  recognizing one exact term, as every clause of a ground clause family does, reports that term as its ground
  field.
\<close>


corollary clause_stated_targets:
  "(Target_Term x\<in>set (pattern_stated (schema_conclusion S)) \<or>
      (\<exists>s l. (s,l)\<in>clause_calls S \<and> Target_Term x\<in>set l) \<or>
      (\<exists>s ls l. (s,ls)\<in>clause_materials S \<and> l\<in>set ls \<and> Target_Term x\<in>set l)) \<longleftrightarrow>
    Target_Term x\<in>schema_leaves S"
  (is "?places \<longleftrightarrow> _")
proof
  assume ?places
  then consider (conclusion) "Target_Term x\<in>pattern_leaves (schema_conclusion S)"
    | (call) s d p where "(s,d,p)\<in>schema_premises S" "Target_Term x\<in>pattern_leaves p"
    | (material) s M q where "(s,M)\<in>schema_material_premises S" "q\<in>set (material_fields M)"
        "Target_Term x\<in>pattern_leaves q"
    by (auto simp: clause_calls_def clause_materials_def material_stated_def pattern_stated_targets)
  then show "Target_Term x\<in>schema_leaves S"
    by cases (force simp: schema_leaves_def material_leaves_def)+
next
  assume "Target_Term x\<in>schema_leaves S"
  then consider (conclusion) "Target_Term x\<in>pattern_leaves (schema_conclusion S)"
    | (call) s d p where "(s,d,p)\<in>schema_premises S" "Target_Term x\<in>pattern_leaves p"
    | (material) s M q where "(s,M)\<in>schema_material_premises S" "q\<in>set (material_fields M)"
        "Target_Term x\<in>pattern_leaves q"
    by (auto simp: schema_leaves_def material_leaves_def)
  then show ?places
  proof cases
    case conclusion
    then show ?thesis by (simp add: pattern_stated_targets)
  next
    case call
    have "(s,pattern_stated p)\<in>clause_calls S" using call(1) by (force simp: clause_calls_def)
    then show ?thesis using call(2) pattern_stated_targets by blast
  next
    case material
    have "(s,material_stated M)\<in>clause_materials S" using material(1) by (force simp: clause_materials_def)
    moreover have "pattern_stated q\<in>set (material_stated M)" using material(2) by (simp add: material_stated_def)
    ultimately show ?thesis using material(3) pattern_stated_targets by blast
  qed
qed

corollary definition_stated_targets:
  "(Target_Term x\<in>set (pattern_stated p) \<or> (\<exists>c S. (c,S)\<in>C \<and>
      (Target_Term x\<in>set (pattern_stated (schema_conclusion S)) \<or>
        (\<exists>s l. (s,l)\<in>clause_calls S \<and> Target_Term x\<in>set l) \<or>
        (\<exists>s ls l. (s,ls)\<in>clause_materials S \<and> l\<in>set ls \<and> Target_Term x\<in>set l)))) \<longleftrightarrow>
    Target_Term x\<in>pattern_leaves p \<union> (\<Union>(c,S)\<in>C. schema_leaves S)"
  by (simp only: clause_stated_targets) (auto simp: pattern_stated_targets)

lemma pattern_ground_exact_term: "pattern_ground (exact_term_pattern x)=Some x"
  by (induction x) simp_all

corollary clause_ground_recognizer: "clause_ground (recognizer_schema (exact_term_pattern x))=[x]"
  by (simp add: clause_ground_def recognizer_schema_def pattern_ground_exact_term)

corollary ground_clause_family_ground:
  assumes "(c,S)\<in>ground_clause_family xs"
  shows "\<exists>i<length xs. c=[i] \<and> clause_ground S=[decode_finite_term (xs!i)]"
  using assms by (auto simp: ground_clause_family_def clause_ground_recognizer)

section \<open>The report's rows, and their presentation\<close>

text \<open>
  A report is presented as lists: the interface's leaves beside the clause rows, each row a clause socket beside
  the clause's ground field, conclusion leaves, call rows and material rows, a material row's operand the
  five field lists of @{const stated_tuple}. The presentation of such rows is composed from the generic pair
  and sequence presentations, so its reader is exact in the form of @{const finite_reads} by the composition
  theorems alone.
\<close>

type_synonym finite_stated_tuple =
  "finite_factor_term list\<times>finite_factor_term list\<times>finite_factor_term list\<times>finite_factor_term list\<times>finite_factor_term list"

type_synonym finite_clause_rows = "finite_factor_term list\<times>finite_factor_term list\<times>
  (local_address\<times>finite_factor_term list) list\<times>(local_address\<times>finite_stated_tuple) list"

type_synonym finite_report_rows = "finite_factor_term list\<times>(local_address\<times>finite_clause_rows) list"

abbreviation finite_leaves_presentation :: "finite_factor_term list \<Rightarrow> finite_factor_term" where
  "finite_leaves_presentation\<equiv>finite_sequence_presentation id"

definition finite_tuple_presentation :: "finite_stated_tuple \<Rightarrow> finite_factor_term" where
  "finite_tuple_presentation=finite_pair_presentation finite_leaves_presentation
    (finite_pair_presentation finite_leaves_presentation (finite_pair_presentation finite_leaves_presentation
      (finite_pair_presentation finite_leaves_presentation finite_leaves_presentation)))"

definition finite_clause_rows_presentation :: "finite_clause_rows \<Rightarrow> finite_factor_term" where
  "finite_clause_rows_presentation=finite_pair_presentation finite_leaves_presentation
    (finite_pair_presentation finite_leaves_presentation
      (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation Finite_Payload finite_leaves_presentation))
        (finite_sequence_presentation (finite_pair_presentation Finite_Payload finite_tuple_presentation))))"

definition finite_report_rows_presentation :: "finite_report_rows \<Rightarrow> finite_factor_term" where
  "finite_report_rows_presentation=finite_pair_presentation finite_leaves_presentation
    (finite_sequence_presentation (finite_pair_presentation Finite_Payload finite_clause_rows_presentation))"

definition finite_leaves_read :: "finite_factor_term \<Rightarrow> finite_factor_term list option" where
  "finite_leaves_read=finite_sequence_read Some"

definition finite_tuple_read :: "finite_factor_term \<Rightarrow> finite_stated_tuple option" where
  "finite_tuple_read=finite_pair_read finite_leaves_read (finite_pair_read finite_leaves_read
    (finite_pair_read finite_leaves_read (finite_pair_read finite_leaves_read finite_leaves_read)))"

definition finite_clause_rows_read :: "finite_factor_term \<Rightarrow> finite_clause_rows option" where
  "finite_clause_rows_read=finite_pair_read finite_leaves_read (finite_pair_read finite_leaves_read
    (finite_pair_read (finite_sequence_read (finite_pair_read finite_payload_value_read finite_leaves_read))
      (finite_sequence_read (finite_pair_read finite_payload_value_read finite_tuple_read))))"

definition finite_report_rows_read :: "finite_factor_term \<Rightarrow> finite_report_rows option" where
  "finite_report_rows_read=finite_pair_read finite_leaves_read
    (finite_sequence_read (finite_pair_read finite_payload_value_read finite_clause_rows_read))"

lemma finite_leaves_reads: "finite_reads finite_leaves_read finite_leaves_presentation"
  unfolding finite_leaves_read_def by (rule finite_sequence_reads) (simp add: finite_reads_def)

lemma finite_tuple_reads: "finite_reads finite_tuple_read finite_tuple_presentation"
  unfolding finite_tuple_read_def finite_tuple_presentation_def by (intro finite_pair_reads finite_leaves_reads)

lemma finite_clause_rows_reads: "finite_reads finite_clause_rows_read finite_clause_rows_presentation"
  unfolding finite_clause_rows_read_def finite_clause_rows_presentation_def
  by (intro finite_pair_reads finite_sequence_reads finite_payload_reads finite_leaves_reads finite_tuple_reads)

lemma finite_report_rows_reads: "finite_reads finite_report_rows_read finite_report_rows_presentation"
  unfolding finite_report_rows_read_def finite_report_rows_presentation_def
  by (intro finite_pair_reads finite_sequence_reads finite_payload_reads finite_leaves_reads finite_clause_rows_reads)

section \<open>The report read in every enumeration\<close>

text \<open>
  The rows of a report are keyed: the clause sockets are distinct, and within a clause the premise sockets.
  The reader reads the rows and keeps them when they are keyed, returning the report's value: the interface's
  leaves and the finite set of clause rows, each with its finite sets of call and material rows. A term is
  read as a value exactly when it presents that value in some keyed enumeration of its rows; a term of
  another shape, or with a repeated socket, presents no report and is refused. Leaves keep their order and
  their repetitions, as the presentation states them.
\<close>

definition finite_tuple_list :: "finite_stated_tuple \<Rightarrow> finite_factor_term list list" where
  "finite_tuple_list z=(case z of (a,b,c,d,e) \<Rightarrow> [a,b,c,d,e])"

definition finite_tuple_of :: "finite_factor_term list list \<Rightarrow> finite_stated_tuple" where
  "finite_tuple_of ls=(ls!0,ls!1,ls!2,ls!3,ls!4)"

type_synonym finite_clause_value = "finite_factor_term list\<times>finite_factor_term list\<times>
  (local_address\<times>finite_factor_term list) fset\<times>(local_address\<times>finite_factor_term list list) fset"

type_synonym finite_report_value = "finite_factor_term list\<times>(local_address\<times>finite_clause_value) fset"

definition finite_clause_rows_keyed :: "finite_clause_rows \<Rightarrow> bool" where
  "finite_clause_rows_keyed w \<longleftrightarrow> (case w of (g,l,qs,ms) \<Rightarrow> distinct (map fst qs) \<and> distinct (map fst ms))"

definition finite_clause_rows_value :: "finite_clause_rows \<Rightarrow> finite_clause_value" where
  "finite_clause_rows_value w=(case w of (g,l,qs,ms) \<Rightarrow>
    (g,l,fset_of_list qs,fset_of_list (map (\<lambda>(s,t). (s,finite_tuple_list t)) ms)))"

definition finite_report_rows_keyed :: "finite_report_rows \<Rightarrow> bool" where
  "finite_report_rows_keyed x \<longleftrightarrow> distinct (map fst (snd x)) \<and> list_all (finite_clause_rows_keyed \<circ> snd) (snd x)"

definition finite_report_rows_value :: "finite_report_rows \<Rightarrow> finite_report_value" where
  "finite_report_rows_value x=(fst x,fset_of_list (map (\<lambda>(c,w). (c,finite_clause_rows_value w)) (snd x)))"

definition finite_report_presents :: "finite_report_value \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_report_presents x t \<longleftrightarrow> (\<exists>w. finite_report_rows_keyed w \<and> finite_report_rows_value w=x \<and>
    t=finite_report_rows_presentation w)"

definition finite_stated_report_read :: "finite_factor_term \<Rightarrow> finite_report_value option" where
  "finite_stated_report_read t=(case finite_report_rows_read t of None \<Rightarrow> None
    | Some w \<Rightarrow> if finite_report_rows_keyed w then Some (finite_report_rows_value w) else None)"

theorem finite_stated_report_read_exact:
  "finite_stated_report_read t=Some x \<longleftrightarrow> finite_report_presents x t"
proof
  assume "finite_stated_report_read t=Some x"
  then obtain w where "finite_report_rows_read t=Some w" "finite_report_rows_keyed w" "finite_report_rows_value w=x"
    by (auto simp: finite_stated_report_read_def split: option.splits if_splits)
  then show "finite_report_presents x t"
    unfolding finite_report_presents_def using finite_readsD[OF finite_report_rows_reads] by blast
next
  assume "finite_report_presents x t"
  then obtain w where "finite_report_rows_keyed w" "finite_report_rows_value w=x" "t=finite_report_rows_presentation w"
    by (auto simp: finite_report_presents_def)
  then show "finite_stated_report_read t=Some x"
    by (simp add: finite_stated_report_read_def finite_reads_present[OF finite_report_rows_reads])
qed

section \<open>The presented rows decode to the report's presentation\<close>

lemma decode_finite_sequence_presentation:
  "decode_finite_term (finite_sequence_presentation f xs)=data_list_term (map (decode_finite_term \<circ> f) xs)"
  by (induction xs) simp_all

definition decode_stated_tuple :: "finite_stated_tuple \<Rightarrow> factor_term list list" where
  "decode_stated_tuple t=map (map decode_finite_term) (finite_tuple_list t)"

lemma decode_finite_tuple:
  "decode_finite_term (finite_tuple_presentation t)=stated_tuple (decode_stated_tuple t)"
  by (cases t rule: prod_cases5) (simp add: finite_tuple_presentation_def finite_pair_presentation_def
    decode_finite_sequence_presentation stated_tuple_def material_tuple_def decode_stated_tuple_def finite_tuple_list_def)

lemma decode_finite_clause_rows:
  "decode_finite_term (finite_clause_rows_presentation (g,l,qs,ms))=
    Pair_Term (data_list_term (map decode_finite_term g)) (Pair_Term (data_list_term (map decode_finite_term l))
      (Pair_Term (data_list_term (map place_term (map (\<lambda>(s,x). (s,map decode_finite_term x)) qs)))
        (data_list_term (map material_place_term (map (\<lambda>(s,t). (s,decode_stated_tuple t)) ms)))))"
  by (simp add: finite_clause_rows_presentation_def finite_pair_presentation_def decode_finite_sequence_presentation
    decode_finite_tuple place_term_def material_place_term_def split_def comp_def)

lemma decode_finite_report_rows:
  "decode_finite_term (finite_report_rows_presentation (l,rs))=Pair_Term (data_list_term (map decode_finite_term l))
    (data_list_term (map (\<lambda>(c,w). Pair_Term (Payload_Term c) (decode_finite_term (finite_clause_rows_presentation w))) rs))"
  by (simp add: finite_report_rows_presentation_def finite_pair_presentation_def decode_finite_sequence_presentation
    split_def comp_def)

section \<open>A clause's rows present its report exactly when they enumerate its computed value\<close>

lemma finite_clause_stated_fields:
  "clause_ground (decode_finite_schema S)=map decode_finite_term (fst (finite_clause_stated S))"
  "pattern_stated (schema_conclusion (decode_finite_schema S))=map decode_finite_term (fst (snd (finite_clause_stated S)))"
  "clause_calls (decode_finite_schema S)=
    (\<lambda>(s,x). (s,map decode_finite_term x)) ` fset (fst (snd (snd (finite_clause_stated S))))"
  "clause_materials (decode_finite_schema S)=
    (\<lambda>(s,xs). (s,map (map decode_finite_term) xs)) ` fset (snd (snd (snd (finite_clause_stated S))))"
proof -
  obtain g l Q M where z: "finite_clause_stated S=(g,l,Q,M)" by (cases "finite_clause_stated S") auto
  have exact: "decode_clause_stated (g,l,Q,M)=clause_stated (decode_finite_schema S)"
    using finite_clause_stated_exact[of S] by (simp only: z)
  show "clause_ground (decode_finite_schema S)=map decode_finite_term (fst (finite_clause_stated S))"
    "pattern_stated (schema_conclusion (decode_finite_schema S))=map decode_finite_term (fst (snd (finite_clause_stated S)))"
    "clause_calls (decode_finite_schema S)=
      (\<lambda>(s,x). (s,map decode_finite_term x)) ` fset (fst (snd (snd (finite_clause_stated S))))"
    "clause_materials (decode_finite_schema S)=
      (\<lambda>(s,xs). (s,map (map decode_finite_term) xs)) ` fset (snd (snd (snd (finite_clause_stated S))))"
    using exact by (simp_all add: z decode_clause_stated_def clause_stated_def)
qed

lemma finite_clause_material_tuple:
  assumes "(s,ls)\<in>fset (snd (snd (snd (finite_clause_stated S))))"
  shows "finite_tuple_list (finite_tuple_of ls)=ls"
  using assms by (auto simp: finite_clause_stated_def finite_material_fields_def finite_tuple_list_def
    finite_tuple_of_def fimage.rep_eq)

lemma stated_fset_of_list_eq: "fset_of_list xs=A \<longleftrightarrow> set xs=fset A"
  by (metis fset_inject fset_of_list.rep_eq)

lemma stated_image_enumeration:
  assumes image: "set ys=f ` A" and injective: "inj f"
  obtains xs where "ys=map f xs" "set xs=A"
proof -
  have members: "\<forall>y\<in>set ys. \<exists>x. y=f x \<and> x\<in>A" using image by auto
  obtain xs where xs: "ys=map f xs" "\<forall>x\<in>set xs. x\<in>A"
    using list_range_restricted_witnesses[of ys f "\<lambda>x. x\<in>A"] members by blast
  have "f ` set xs=f ` A" using xs(1) image by simp
  then have "set xs=A" by (simp only: inj_image_eq_iff[OF injective])
  then show ?thesis using that xs(1) by blast
qed

lemma stated_keyed_inj: "inj f \<Longrightarrow> inj (\<lambda>(k,x). (k,f x))"
  by (auto simp: inj_def)

lemma stated_decode_leaves_inj: "inj (map decode_finite_term)"
  by (rule inj_mapI) (simp add: inj_def)

lemma stated_decode_lists_inj: "inj (map (map decode_finite_term))"
  by (rule inj_mapI) (rule stated_decode_leaves_inj)

lemma finite_clause_rows_stated:
  assumes keyed: "finite_clause_rows_keyed w" and valued: "finite_clause_rows_value w=finite_clause_stated S"
  shows "clause_stated_presents (decode_finite_schema S) (decode_finite_term (finite_clause_rows_presentation w))"
proof -
  obtain g l qs ms where w: "w=(g,l,qs,ms)" by (cases w) auto
  have fields: "fst (finite_clause_stated S)=g" "fst (snd (finite_clause_stated S))=l"
      "fst (snd (snd (finite_clause_stated S)))=fset_of_list qs"
      "snd (snd (snd (finite_clause_stated S)))=fset_of_list (map (\<lambda>(s,t). (s,finite_tuple_list t)) ms)"
    using valued[symmetric] by (simp_all add: w finite_clause_rows_value_def)
  have keys: "distinct (map fst qs)" "distinct (map fst ms)" using keyed by (simp_all add: w finite_clause_rows_keyed_def)
  let ?qs="map (\<lambda>(s,x). (s,map decode_finite_term x)) qs"
  let ?ms="map (\<lambda>(s,t). (s,decode_stated_tuple t)) ms"
  have calls: "set ?qs=clause_calls (decode_finite_schema S)"
    by (simp add: finite_clause_stated_fields(3) fields(3) fset_of_list.rep_eq)
  have materials: "set ?ms=clause_materials (decode_finite_schema S)"
    by (simp add: finite_clause_stated_fields(4) fields(4) fset_of_list.rep_eq image_image split_def
      decode_stated_tuple_def)
  have qk: "distinct (map fst ?qs)" using keys(1) by (simp add: comp_def split_def)
  have mk: "distinct (map fst ?ms)" using keys(2) by (simp add: comp_def split_def)
  have shape: "decode_finite_term (finite_clause_rows_presentation w)=
      Pair_Term (data_list_term (clause_ground (decode_finite_schema S)))
        (Pair_Term (data_list_term (pattern_stated (schema_conclusion (decode_finite_schema S))))
          (Pair_Term (data_list_term (map place_term ?qs)) (data_list_term (map material_place_term ?ms))))"
    by (simp only: w decode_finite_clause_rows finite_clause_stated_fields(1,2) fields(1,2))
  show ?thesis unfolding clause_stated_presents_def using qk calls mk materials shape by blast
qed

lemma finite_clause_rows_enumeration:
  assumes presents: "clause_stated_presents (decode_finite_schema S) v"
  obtains w where "finite_clause_rows_keyed w" "finite_clause_rows_value w=finite_clause_stated S"
    "v=decode_finite_term (finite_clause_rows_presentation w)"
proof -
  obtain g l Q M where z: "finite_clause_stated S=(g,l,Q,M)" by (cases "finite_clause_stated S") auto
  obtain qs0 ms0 where qk: "distinct (map fst qs0)" and qset: "set qs0=clause_calls (decode_finite_schema S)"
      and mk: "distinct (map fst ms0)" and mset: "set ms0=clause_materials (decode_finite_schema S)"
      and v: "v=Pair_Term (data_list_term (clause_ground (decode_finite_schema S)))
        (Pair_Term (data_list_term (pattern_stated (schema_conclusion (decode_finite_schema S))))
          (Pair_Term (data_list_term (map place_term qs0)) (data_list_term (map material_place_term ms0))))"
    using presents unfolding clause_stated_presents_def by blast
  have fields: "clause_ground (decode_finite_schema S)=map decode_finite_term g"
      "pattern_stated (schema_conclusion (decode_finite_schema S))=map decode_finite_term l"
      "clause_calls (decode_finite_schema S)=(\<lambda>(s,x). (s,map decode_finite_term x)) ` fset Q"
      "clause_materials (decode_finite_schema S)=(\<lambda>(s,xs). (s,map (map decode_finite_term) xs)) ` fset M"
    using finite_clause_stated_fields[of S] by (simp_all add: z)
  obtain qs where qs: "qs0=map (\<lambda>(s,x). (s,map decode_finite_term x)) qs" "set qs=fset Q"
    by (rule stated_image_enumeration[OF qset[unfolded fields(3)] stated_keyed_inj[OF stated_decode_leaves_inj]])
  obtain ls where ls: "ms0=map (\<lambda>(s,xs). (s,map (map decode_finite_term) xs)) ls" "set ls=fset M"
    by (rule stated_image_enumeration[OF mset[unfolded fields(4)] stated_keyed_inj[OF stated_decode_lists_inj]])
  let ?ms="map (\<lambda>(s,xs). (s,finite_tuple_of xs)) ls"
  have tuple: "finite_tuple_list (finite_tuple_of xs)=xs" if "(s,xs)\<in>set ls" for s xs
    using finite_clause_material_tuple[of s xs S] that ls(2) z by simp
  have tuples: "map (\<lambda>(s,t). (s,finite_tuple_list t)) ?ms=ls"
  proof (simp only: map_map, rule map_idI)
    fix y assume y: "y\<in>set ls"
    obtain s xs where sy: "y=(s,xs)" by (cases y)
    show "((\<lambda>(s,t). (s,finite_tuple_list t)) \<circ> (\<lambda>(s,xs). (s,finite_tuple_of xs))) y=y"
      using tuple[of s xs] y sy by simp
  qed
  have mseq: "ms0=map (\<lambda>(s,t). (s,decode_stated_tuple t)) ?ms"
  proof -
    have "map (\<lambda>(s,t). (s,decode_stated_tuple t)) ?ms=
        map (\<lambda>(s,xs). (s,map (map decode_finite_term) xs)) (map (\<lambda>(s,t). (s,finite_tuple_list t)) ?ms)"
      by (simp add: decode_stated_tuple_def split_def)
    then show ?thesis by (simp only: tuples ls(1))
  qed
  have qk': "distinct (map fst qs)" using qk by (simp add: qs(1) split_def comp_def)
  have mk': "distinct (map fst ?ms)" using mk by (simp add: ls(1) split_def comp_def)
  have qf: "fset_of_list qs=Q" using qs(2) by (simp only: stated_fset_of_list_eq)
  have mf: "fset_of_list (map (\<lambda>(s,t). (s,finite_tuple_list t)) ?ms)=M"
    using ls(2) by (simp only: tuples stated_fset_of_list_eq)
  show ?thesis
  proof (rule that[of "(g,l,qs,?ms)"])
    show "finite_clause_rows_keyed (g,l,qs,?ms)" using qk' mk' by (simp add: finite_clause_rows_keyed_def)
    show "finite_clause_rows_value (g,l,qs,?ms)=finite_clause_stated S"
      using qf mf by (simp add: finite_clause_rows_value_def z)
    show "v=decode_finite_term (finite_clause_rows_presentation (g,l,qs,?ms))"
      by (simp only: v decode_finite_clause_rows fields(1,2) qs(1) mseq)
  qed
qed

section \<open>A report matches a definition's computed report exactly when it presents the definition's report\<close>

text \<open>
  The report read from a term matches a computed value when it holds the same interface leaves, the same clause
  sockets, and only rows of that value. At a definition's computed report this is exactly the report's native
  presentation, @{const definition_stated_presents}, in every enumeration.
\<close>

definition finite_report_matches :: "finite_report_value \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "finite_report_matches D t=(case finite_stated_report_read t of None \<Rightarrow> False
    | Some x \<Rightarrow> fst x=fst D \<and> fimage fst (snd x)=fimage fst (snd D) \<and> snd x |\<subseteq>| snd D)"

theorem finite_report_matches_stated:
  "finite_report_matches (finite_definition_stated q F) t \<longleftrightarrow>
    definition_stated_presents (decode_finite_pattern q) (map_relation_values decode_finite_schema (fset F))
      (decode_finite_term t)"
  (is "?matches \<longleftrightarrow> definition_stated_presents ?p ?C ?t")
proof -
  let ?D="finite_definition_stated q F"
  have leaves: "map decode_finite_term (fst ?D)=pattern_stated ?p"
    by (simp add: finite_definition_stated_def finite_pattern_stated_exact)
  have rows: "snd ?D=fimage (\<lambda>(c,S). (c,finite_clause_stated S)) F" by (simp add: finite_definition_stated_def)
  have domain: "rel_dom ?C=fst ` fset F" by (simp add: rel_dom_image)
  have member: "(c,S')\<in>?C \<longleftrightarrow> (\<exists>S. (c,S)\<in>fset F \<and> S'=decode_finite_schema S)" for c S'
    by auto
  show ?thesis
  proof
    assume ?matches
    then obtain x where read: "finite_stated_report_read t=Some x" and same: "fst x=fst ?D"
        "fimage fst (snd x)=fimage fst (snd ?D)" and included: "snd x |\<subseteq>| snd ?D"
      by (auto simp: finite_report_matches_def split: option.splits)
    obtain w where "finite_report_rows_keyed w" "finite_report_rows_value w=x" "t=finite_report_rows_presentation w"
      using read unfolding finite_stated_report_read_exact finite_report_presents_def by blast
    moreover obtain l rs where "w=(l,rs)" by (cases w)
    ultimately have keyed: "finite_report_rows_keyed (l,rs)" and xv: "x=finite_report_rows_value (l,rs)"
        and t: "t=finite_report_rows_presentation (l,rs)" by simp_all
    let ?ks="map (\<lambda>(c,w). (c,decode_finite_term (finite_clause_rows_presentation w))) rs"
    have kd: "distinct (map fst ?ks)" using keyed by (simp add: finite_report_rows_keyed_def split_def comp_def)
    have keys: "fst ` set ?ks=rel_dom ?C"
    proof -
      have "fst ` set ?ks=fst ` set rs" by (simp add: image_image split_def)
      also have "...=fset (fimage fst (snd x))"
        by (simp add: xv finite_report_rows_value_def fimage.rep_eq fset_of_list.rep_eq image_image split_def)
      also have "...=fst ` fset F" using same(2) by (simp add: rows fimage.rep_eq image_image split_def)
      finally show ?thesis by (simp only: domain)
    qed
    have clauses: "\<exists>S'. (c,S')\<in>?C \<and> clause_stated_presents S' v" if kv: "(c,v)\<in>set ?ks" for c v
    proof -
      obtain w where w: "(c,w)\<in>set rs" "v=decode_finite_term (finite_clause_rows_presentation w)" using kv by auto
      have wk: "finite_clause_rows_keyed w" using keyed w(1) by (auto simp: finite_report_rows_keyed_def list_all_iff)
      have "(c,finite_clause_rows_value w)\<in>fset (snd x)"
        using w(1) by (auto simp: xv finite_report_rows_value_def fset_of_list.rep_eq)
      then have "(c,finite_clause_rows_value w)\<in>fset (snd ?D)" using included by (auto simp: less_eq_fset.rep_eq)
      then obtain S where S: "(c,S)\<in>fset F" "finite_clause_rows_value w=finite_clause_stated S"
        by (auto simp: rows fimage.rep_eq)
      show ?thesis using finite_clause_rows_stated[OF wk S(2)] S(1) w(2) member by blast
    qed
    have ld: "map decode_finite_term l=pattern_stated ?p" using same(1) leaves by (simp add: xv finite_report_rows_value_def)
    have tdecode: "?t=Pair_Term (data_list_term (pattern_stated ?p)) (data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ?ks))"
      by (simp add: t decode_finite_report_rows ld map_map comp_def split_def)
    show "definition_stated_presents ?p ?C ?t" unfolding definition_stated_presents_def using kd keys clauses tdecode by blast
  next
    assume "definition_stated_presents ?p ?C ?t"
    then obtain ks where kd: "distinct (map fst ks)" and keys: "fst ` set ks=rel_dom ?C"
        and clauses: "\<And>c v. (c,v)\<in>set ks \<Longrightarrow> \<exists>S'. (c,S')\<in>?C \<and> clause_stated_presents S' v"
        and tdecode: "?t=Pair_Term (data_list_term (pattern_stated ?p)) (data_list_term (map (\<lambda>(c,v). Pair_Term (Payload_Term c) v) ks))"
      unfolding definition_stated_presents_def by blast
    define present_row where "present_row=(\<lambda>(c::local_address,w). (c,decode_finite_term (finite_clause_rows_presentation w)))"
    define row_ok where "row_ok=(\<lambda>(c::local_address,w). finite_clause_rows_keyed w \<and> (c,finite_clause_rows_value w)\<in>fset (snd ?D))"
    have element: "\<exists>z. y=present_row z \<and> row_ok z" if y: "y\<in>set ks" for y
    proof -
      obtain c v where cv: "y=(c,v)" by (cases y)
      obtain S' where S': "(c,S')\<in>?C" "clause_stated_presents S' v" using clauses y cv by blast
      obtain S where S: "(c,S)\<in>fset F" "S'=decode_finite_schema S" using S'(1) member by blast
      obtain w where w: "finite_clause_rows_keyed w" "finite_clause_rows_value w=finite_clause_stated S"
          "v=decode_finite_term (finite_clause_rows_presentation w)"
        using finite_clause_rows_enumeration S'(2) S(2) by blast
      have "(c,finite_clause_rows_value w)\<in>fset (snd ?D)" using S(1) w(2) by (force simp: rows fimage.rep_eq)
      then show ?thesis using w cv by (intro exI[of _ "(c,w)"]) (simp add: present_row_def row_ok_def)
    qed
    obtain rs where rs: "ks=map present_row rs" "\<forall>z\<in>set rs. row_ok z"
      using list_range_restricted_witnesses[of ks present_row row_ok] element by blast
    have kr: "map fst ks=map fst rs" by (simp add: rs(1) present_row_def split_def comp_def)
    have keyed: "finite_report_rows_keyed (fst ?D,rs)"
      using kd kr rs(2) by (auto simp: finite_report_rows_keyed_def list_all_iff row_ok_def split_def)
    have t: "t=finite_report_rows_presentation (fst ?D,rs)"
    proof -
      have "decode_finite_term t=decode_finite_term (finite_report_rows_presentation (fst ?D,rs))"
        by (simp add: tdecode decode_finite_report_rows leaves rs(1) present_row_def map_map comp_def split_def)
      then show ?thesis by simp
    qed
    have xv: "finite_stated_report_read t=Some (finite_report_rows_value (fst ?D,rs))"
      unfolding finite_stated_report_read_exact finite_report_presents_def using keyed t by blast
    have k1: "fst ` set rs=fst ` fset F"
    proof -
      have "fst ` set rs=fst ` set ks" using kr by (metis set_map)
      then show ?thesis by (simp only: keys domain)
    qed
    have k2: "fimage fst (snd (finite_report_rows_value (fst ?D,rs)))=fimage fst (snd ?D)"
    proof -
      have "fset (fimage fst (snd (finite_report_rows_value (fst ?D,rs))))=fst ` set rs"
        by (simp add: finite_report_rows_value_def fimage.rep_eq fset_of_list.rep_eq image_image split_def)
      also have "...=fset (fimage fst (snd ?D))" using k1 by (simp add: rows fimage.rep_eq image_image split_def)
      finally show ?thesis by (simp only: fset_inject)
    qed
    have k3: "snd (finite_report_rows_value (fst ?D,rs)) |\<subseteq>| snd ?D"
      using rs(2) by (auto simp: finite_report_rows_value_def less_eq_fset.rep_eq fset_of_list.rep_eq row_ok_def split_def)
    show ?matches using xv k2 k3 by (simp add: finite_report_matches_def finite_report_rows_value_def)
  qed
qed

section \<open>The counterpart of the stated-leaves reader (590)\<close>

definition finite_stated_report :: "finite_factor_term \<Rightarrow> bool" where
  "finite_stated_report t=(case t of Finite_Pair a y \<Rightarrow> (case finite_source_root_read a of None \<Rightarrow> False
      | Some ((E,u),r) \<Rightarrow> fBex (finite_native_definition_readings E u r)
          (\<lambda>(p,F). finite_report_matches (finite_definition_stated p F) y))
    | _ \<Rightarrow> False)"

theorem finite_stated_report_exact:
  "finite_stated_report t \<longleftrightarrow> stated_report_result (decode_finite_term t)"
proof
  assume holds: "finite_stated_report t"
  obtain a b where ab: "t=Finite_Pair a b" using holds by (cases t) (simp_all add: finite_stated_report_def)
  obtain E u r where read: "finite_source_root_read a=Some ((E,u),r)"
    using holds by (cases "finite_source_root_read a") (auto simp: finite_stated_report_def ab)
  obtain p F where reading: "(p,F) |\<in>| finite_native_definition_readings E u r"
      and matches: "finite_report_matches (finite_definition_stated p F) b"
    using holds read by (auto simp: finite_stated_report_def ab)
  obtain e where argument: "decode_finite_term a=source_root_argument e (use_data_term u) (Payload_Term r)"
      and source: "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp only: finite_source_root_read_exact)
  have defined: "native_definition_at (decode_finite_environment E) u r (decode_finite_pattern p)
      (map_relation_values decode_finite_schema (fset F))"
    using reading by (simp only: finite_native_definition_readings_correct)
  have presents: "definition_stated_presents (decode_finite_pattern p) (map_relation_values decode_finite_schema (fset F))
      (decode_finite_term b)"
    using matches by (simp only: finite_report_matches_stated)
  have "decode_finite_term t=Pair_Term (source_root_argument e (use_data_term u) (Payload_Term r)) (decode_finite_term b)"
    by (simp add: ab argument)
  then show "stated_report_result (decode_finite_term t)" using source defined presents by blast
next
  assume "stated_report_result (decode_finite_term t)"
  then obtain E e u r p C y where z: "decode_finite_term t=Pair_Term (source_root_argument e (use_data_term u) (Payload_Term r)) y"
      and source: "environment_value_presents E e" and defined: "native_definition_at E u r p C"
      and presents: "definition_stated_presents p C y" by blast
  obtain a b where ab: "t=Finite_Pair a b" using z by (cases t) auto
  have ad: "decode_finite_term a=source_root_argument e (use_data_term u) (Payload_Term r)"
      and bd: "decode_finite_term b=y" using z by (simp_all add: ab)
  obtain G where decoded: "decode_finite_environment G=E" by (rule environment_value_presents_finite[OF source])
  have read: "finite_source_root_read a=Some ((G,u),r)"
    unfolding finite_source_root_read_exact using ad source decoded by blast
  obtain q F where reading: "(q,F) |\<in>| finite_native_definition_readings G u r"
      and pattern: "decode_finite_pattern q=p" and clauses: "map_relation_values decode_finite_schema (fset F)=C"
    using finite_native_definition_readings_complete[of G u r p C] defined decoded by blast
  have matches: "finite_report_matches (finite_definition_stated q F) b"
    by (simp only: finite_report_matches_stated pattern clauses bd presents)
  show "finite_stated_report t"
    unfolding finite_stated_report_def ab using read reading matches by (auto intro!: fBexI[where x="(q,F)"])
qed

corollary finite_stated_report_meaning:
  "finite_stated_report t \<longleftrightarrow> (590,decode_finite_term t)\<in>positive_meaning stated_report_system"
  by (simp only: finite_stated_report_exact stated_report_exact)

section \<open>Controls\<close>

text \<open>
  Two one-definition programs, installed as the extension of the empty program as the audit's controls are:
  each definition has a variable interface and two premise-free clauses, the first ground and stating a target
  leaf (the whole empty artifact) or the empty payload alone, the second a variable. At the installed site the
  report is presented in the enumeration of its clause rows by socket and in the reverse one, both accepted,
  and with one clause row missing, refused; by @{thm [source] finite_stated_report_meaning} each outcome is
  590's positive meaning at the same term. The native reader's own costs by construction (every clause read
  twice, by 72 and 65, the interface twice, and each target literal's artifact projected by 45 at each
  occurrence) are costs of a native evaluation no evaluator runs (the reader is not head-covered); the
  counterpart computes the leaves once per pattern and reads the definition once.
\<close>

definition stated_counterpart_program :: "nat finite_term_pattern \<Rightarrow> (nat,nat,nat,nat) finite_schema_system" where
  "stated_counterpart_program g=\<lparr>finite_system_interfaces={|(0,Finite_Variable 0)|},
    finite_system_clauses={|((0,0),\<lparr>finite_schema_conclusion=g,finite_schema_premises={||},finite_schema_materials={||}\<rparr>),
      ((0,1),\<lparr>finite_schema_conclusion=Finite_Variable 0,finite_schema_premises={||},finite_schema_materials={||}\<rparr>)|}\<rparr>"

definition stated_counterpart_installed :: "nat finite_term_pattern \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option) option" where
  "stated_counterpart_installed g=finite_extend_mapped_native (fst audit_control_selection) empty_installation_program
    (stated_counterpart_program g) (\<lambda>_. (None,[]))"

definition stated_clause_enumeration :: "finite_clause_value \<Rightarrow> finite_clause_rows" where
  "stated_clause_enumeration z=(case z of (g,l,Q,M) \<Rightarrow> (g,l,finite_functional_rows Q,
    map (\<lambda>(s,ls). (s,finite_tuple_of ls)) (finite_functional_rows M)))"

definition stated_report_enumeration ::
    "((local_address\<times>finite_clause_rows) list \<Rightarrow> (local_address\<times>finite_clause_rows) list) \<Rightarrow>
      finite_report_value \<Rightarrow> finite_factor_term" where
  "stated_report_enumeration arrange D=finite_report_rows_presentation (fst D,
    arrange (map (\<lambda>(c,z). (c,stated_clause_enumeration z)) (finite_functional_rows (snd D))))"

definition stated_counterpart_control :: "nat finite_term_pattern \<Rightarrow>
    ((finite_factor_term list\<times>finite_factor_term list fset)\<times>nat\<times>bool\<times>bool\<times>bool) fset option" where
  "stated_counterpart_control g=(case stated_counterpart_installed g of None \<Rightarrow> None
    | Some (K,w) \<Rightarrow> map_option (\<lambda>R. ffUnion (fimage (\<lambda>d. fimage (\<lambda>(p,F).
        (let D=finite_definition_stated p F;
          decide=(\<lambda>arrange. finite_stated_report (Finite_Pair (finite_source_root_term K d)
            (stated_report_enumeration arrange D))) in
        ((fst D,fimage (\<lambda>(c,z). fst z) (snd D)),fcard (snd D),decide id,decide rev,decide tl)))
          (finite_native_definition_readings K (fst d) (snd d)))
      (finite_system_definitions R))) (finite_native_source K w []))"

ML \<open>
  val stated_counterpart_context = @{context};
  fun stated_counterpart_run name t =
    let
      val (time, value) = Timing.timing (Code_Evaluation.dynamic_value_strict stated_counterpart_context) t;
    in
      writeln ("STATED_COUNTERPART " ^ name ^ " " ^ Timing.message time);
      writeln (Syntax.string_of_term stated_counterpart_context value)
    end;
  val _ = stated_counterpart_run "target" @{term "stated_counterpart_control stated_control_target"};
  val _ = stated_counterpart_run "empty" @{term "stated_counterpart_control (Finite_Pattern_Payload [])"};
\<close>

end
