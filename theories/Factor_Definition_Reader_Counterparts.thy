theory Factor_Definition_Reader_Counterparts
  imports Factor_Package_Reader_Counterparts Factor_Definition_Edge_Reading Factor_Executable_Matching
    Factor_Executable_Packages
begin

text \<open>
  The counterparts of the definition readers 72 (definition call admission), 81 (definition clause reading)
  and 82 (definition edge reading), build C4 of DECISIONS.md "The native evaluator evaluates above an
  implemented base: the given's readers enter through counterparts exact to their native definitions". Each
  is a function on finite terms: it reads its reader's argument back through the finite readers of C1 and
  C2, each exact to its notion, is false on every term not of that shape, and decides on what it read by the
  finite definition readings (@{const finite_native_definition_readings}), the finite matching
  (@{const finite_pattern_accepts}), the finite record and family candidates and the finite schema
  dependencies, each already exact to its notion. Each is exact at every finite term to its reader's result
  relation, and so to the site's positive meaning in its reader's own system. The native definitions stay
  normative: the exactness is the proof.
\<close>

section \<open>A citation observation argument read back\<close>

text \<open>
  The argument of 72 and 81 is an environment value beside a use, beside an address and an operand
  (@{const citation_observation_argument}), read by @{const finite_citation_argument_read} of
  @{text Factor_Package_Reader_Counterparts} at an operand reader exact to its own relation; 79's root
  family reader there is its instance too.
\<close>

lemma finite_operand_read_exact: "Some v=Some y \<longleftrightarrow> decode_finite_term v=decode_finite_term y"
  by (simp add: decode_finite_term_injective)

lemma finite_socket_read_exact:
  "finite_pair_read finite_payload_value_read finite_payload_value_read v=Some y \<longleftrightarrow>
    decode_finite_term v=Pair_Term (Payload_Term (fst y)) (Payload_Term (snd y))"
proof -
  obtain c a where y: "y=(c,a)" by (cases y)
  show ?thesis
    by (simp add: y finite_pair_read_present[where P="\<lambda>r w. w=Payload_Term r" and Q="\<lambda>r w. w=Payload_Term r",
      OF finite_payload_value_read_exact finite_payload_value_read_exact])
qed

abbreviation finite_call_argument_read where
  "finite_call_argument_read\<equiv>finite_citation_argument_read Some"

abbreviation finite_clause_argument_read where
  "finite_clause_argument_read\<equiv>
    finite_citation_argument_read (finite_pair_read finite_payload_value_read finite_payload_value_read)"

lemmas finite_call_argument_read_exact=
  finite_citation_argument_read_exact[where Q="\<lambda>y w. w=decode_finite_term y", OF finite_operand_read_exact]

lemmas finite_clause_argument_read_exact=
  finite_citation_argument_read_exact[where Q="\<lambda>y w. w=Pair_Term (Payload_Term (fst y)) (Payload_Term (snd y))",
    OF finite_socket_read_exact]

section \<open>The counterpart of definition call admission (72)\<close>

text \<open>
  The call is admitted when some reading of the definition at the argument's environment, use and address
  has an interface the operand matches (@{thm [source] finite_pattern_accepts_correct}).
\<close>

definition finite_definition_call_admission_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_definition_call_admission_decision t=(case finite_call_argument_read t of None \<Rightarrow> False
    | Some ((E,u),(r,x)) \<Rightarrow> fBex (finite_native_definition_readings E u r) (\<lambda>(p,F). finite_pattern_accepts p x))"

theorem finite_definition_call_admission_decision_exact:
  "finite_definition_call_admission_decision t \<longleftrightarrow> definition_call_admission_result (decode_finite_term t)"
proof
  assume holds: "finite_definition_call_admission_decision t"
  obtain E u r x where read: "finite_call_argument_read t=Some ((E,u),(r,x))"
    using holds by (cases "finite_call_argument_read t")
      (auto simp: finite_definition_call_admission_decision_def split: prod.splits)
  obtain p F where reading: "(p,F) |\<in>| finite_native_definition_readings E u r"
      and accepts: "finite_pattern_accepts p x"
    using holds read by (auto simp: finite_definition_call_admission_decision_def)
  obtain e where z: "decode_finite_term t=citation_observation_argument e (use_data_term u) (Payload_Term r)
      (decode_finite_term x)"
    and pe: "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp: finite_call_argument_read_exact)
  have "native_definition_at (decode_finite_environment E) u r (decode_finite_pattern p)
      (map_relation_values decode_finite_schema (fset F))"
    using reading by (simp only: finite_native_definition_readings_correct)
  moreover have "pattern_accepts (decode_finite_pattern p) (decode_finite_term x)"
    using accepts by (simp only: finite_pattern_accepts_correct)
  ultimately show "definition_call_admission_result (decode_finite_term t)" using z pe by blast
next
  assume "definition_call_admission_result (decode_finite_term t)"
  then obtain E e u r p C w where z: "decode_finite_term t=citation_observation_argument e (use_data_term u)
      (Payload_Term r) w"
    and pe: "environment_value_presents E e" and defined: "native_definition_at E u r p C"
    and accepts: "pattern_accepts p w"
    by blast
  obtain G where g: "decode_finite_environment G=E" by (rule environment_value_presents_finite[OF pe])
  obtain x where x: "decode_finite_term x=w" using z unfolding decode_finite_pair_iff by blast
  have read: "finite_call_argument_read t=Some ((G,u),(r,x))"
    using z pe by (auto simp: finite_call_argument_read_exact g x)
  obtain q F where reading: "(q,F) |\<in>| finite_native_definition_readings G u r"
      and pattern: "decode_finite_pattern q=p"
    using finite_native_definition_readings_complete[of G u r p C] defined g by blast
  have "finite_pattern_accepts q x" using accepts by (simp add: finite_pattern_accepts_correct pattern x)
  then show "finite_definition_call_admission_decision t"
    using read by (simp add: finite_definition_call_admission_decision_def) (rule fBexI[OF _ reading], simp)
qed

corollary finite_definition_call_admission_decision_meaning:
  "finite_definition_call_admission_decision t \<longleftrightarrow>
    (72,decode_finite_term t)\<in>positive_meaning definition_call_admission_system"
  by (simp only: finite_definition_call_admission_decision_exact definition_call_admission_exact)

section \<open>The counterpart of definition clause reading (81)\<close>

text \<open>
  The operand is a clause socket beside a schema root. The reading holds when a definition stands at the
  argument's environment, use and address and the pair is a row of the clause family its record's second
  field reaches: the rows are those of the finite family candidates at the second field of every two-field
  record the finite record reading recovers at the address, in every artifact at the use.
\<close>

definition finite_clause_rows :: "'u finite_artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    (local_address\<times>local_address) fset" where
  "finite_clause_rows E u r=ffUnion (fimage (\<lambda>C. finite_two_field_record C r
    (\<lambda>ps i m. ffUnion (finite_family_candidates C m))) (finite_artifacts_at E u))"

lemma finite_clause_rows_member:
  "(c,a) |\<in>| finite_clause_rows E u r \<longleftrightarrow> (\<exists>R ps i m M. artifact_at (decode_finite_environment E) u R \<and>
    record_at R r ps [i,m] \<and> family_at R m M \<and> (c,a)\<in>M)"
proof
  assume "(c,a) |\<in>| finite_clause_rows E u r"
  then obtain C where artifact: "C |\<in>| finite_artifacts_at E u"
      and row: "(c,a) |\<in>| finite_two_field_record C r (\<lambda>ps i m. ffUnion (finite_family_candidates C m))"
    by (auto simp: finite_clause_rows_def ffUnion.rep_eq fimage.rep_eq)
  obtain ps i m M where "record_at (decode_finite_object C) r ps [i,m]" "M |\<in>| finite_family_candidates C m"
      "(c,a) |\<in>| M"
    using row by (auto simp: finite_two_field_record_member ffUnion.rep_eq)
  moreover have "artifact_at (decode_finite_environment E) u (decode_finite_object C)"
    using artifact finite_artifacts_at_complete[of E u "decode_finite_object C"] by blast
  ultimately show "\<exists>R ps i m M. artifact_at (decode_finite_environment E) u R \<and>
      record_at R r ps [i,m] \<and> family_at R m M \<and> (c,a)\<in>M"
    using finite_family_candidates_correct[of M C m] by blast
next
  assume "\<exists>R ps i m M. artifact_at (decode_finite_environment E) u R \<and>
      record_at R r ps [i,m] \<and> family_at R m M \<and> (c,a)\<in>M"
  then obtain R ps i m M where parts: "artifact_at (decode_finite_environment E) u R" "record_at R r ps [i,m]"
      "family_at R m M" "(c,a)\<in>M"
    by blast
  obtain C where artifact: "C |\<in>| finite_artifacts_at E u" and decoded: "decode_finite_object C=R"
    using parts(1) finite_artifacts_at_complete[of E u R] by blast
  obtain F where family: "F |\<in>| finite_family_candidates C m" and rows: "fset F=M"
    using finite_family_candidates_complete[of C m M] parts(3) decoded by blast
  have "(c,a) |\<in>| finite_two_field_record C r (\<lambda>ps i m. ffUnion (finite_family_candidates C m))"
    using parts(2,4) decoded family rows by (auto simp: finite_two_field_record_member ffUnion.rep_eq)
  then show "(c,a) |\<in>| finite_clause_rows E u r"
    using artifact by (auto simp: finite_clause_rows_def ffUnion.rep_eq fimage.rep_eq)
qed

definition finite_definition_clause_reading_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_definition_clause_reading_decision t=(case finite_clause_argument_read t of None \<Rightarrow> False
    | Some ((E,u),(r,(c,a))) \<Rightarrow>
      finite_native_definition_readings E u r\<noteq>{||} \<and> (c,a) |\<in>| finite_clause_rows E u r)"

theorem finite_definition_clause_reading_decision_exact:
  "finite_definition_clause_reading_decision t \<longleftrightarrow> definition_clause_reading_result (decode_finite_term t)"
proof
  assume holds: "finite_definition_clause_reading_decision t"
  obtain E u r c a where read: "finite_clause_argument_read t=Some ((E,u),(r,(c,a)))"
    using holds by (cases "finite_clause_argument_read t")
      (auto simp: finite_definition_clause_reading_decision_def split: prod.splits)
  have parts: "finite_native_definition_readings E u r\<noteq>{||}" "(c,a) |\<in>| finite_clause_rows E u r"
    using holds read by (simp_all add: finite_definition_clause_reading_decision_def)
  obtain e where z: "decode_finite_term t=citation_observation_argument e (use_data_term u) (Payload_Term r)
      (Pair_Term (Payload_Term c) (Payload_Term a))"
    and pe: "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp: finite_clause_argument_read_exact)
  obtain p C where "native_definition_at (decode_finite_environment E) u r p C"
    using parts(1) finite_native_definition_readings_nonempty[of E u r] by blast
  moreover obtain R ps i m M where "artifact_at (decode_finite_environment E) u R" "record_at R r ps [i,m]"
      "family_at R m M" "(c,a)\<in>M"
    using parts(2) unfolding finite_clause_rows_member by blast
  ultimately show "definition_clause_reading_result (decode_finite_term t)" using z pe by blast
next
  assume "definition_clause_reading_result (decode_finite_term t)"
  then obtain E e u r p C R ps i m M c a where z: "decode_finite_term t=citation_observation_argument e
      (use_data_term u) (Payload_Term r) (Pair_Term (Payload_Term c) (Payload_Term a))"
    and pe: "environment_value_presents E e" and defined: "native_definition_at E u r p C"
    and parts: "artifact_at E u R" "record_at R r ps [i,m]" "family_at R m M" "(c,a)\<in>M"
    by blast
  obtain G where g: "decode_finite_environment G=E" by (rule environment_value_presents_finite[OF pe])
  have read: "finite_clause_argument_read t=Some ((G,u),(r,(c,a)))"
    using z pe by (auto simp: finite_clause_argument_read_exact g)
  have "finite_native_definition_readings G u r\<noteq>{||}"
    using defined finite_native_definition_readings_nonempty[of G u r] g by blast
  moreover have "(c,a) |\<in>| finite_clause_rows G u r"
    using parts unfolding finite_clause_rows_member g by blast
  ultimately show "finite_definition_clause_reading_decision t"
    using read by (simp add: finite_definition_clause_reading_decision_def)
qed

corollary finite_definition_clause_reading_decision_meaning:
  "finite_definition_clause_reading_decision t \<longleftrightarrow>
    (81,decode_finite_term t)\<in>positive_meaning definition_clause_reading_system"
  by (simp only: finite_definition_clause_reading_decision_exact definition_clause_reading_exact)

section \<open>The counterpart of definition edge reading (82)\<close>

text \<open>
  The argument is an environment value beside two definition sites. The edge holds when some reading of the
  definition at the first site has a clause whose finite schema dependencies hold the second
  (@{thm [source] finite_schema_dependencies_correct}): the definition edges of
  @{const native_definition_edges} at one source, read at that source alone.
\<close>

lemma finite_definition_edges_at:
  "fBex (finite_native_definition_readings E (fst d) (snd d))
      (\<lambda>(p,F). fBex F (\<lambda>(c,S). f |\<in>| finite_schema_dependencies S)) \<longleftrightarrow>
    (d,f)\<in>native_definition_edges (decode_finite_environment E)"
proof -
  have rows: "(d,p,F) |\<in>| finite_native_definition_rows E \<longleftrightarrow>
      (p,F) |\<in>| finite_native_definition_readings E (fst d) (snd d)" for p F
    by (simp only: finite_native_definition_rows_correct finite_native_definition_readings_correct)
  have "(d,f) |\<in>| finite_native_definition_edges E \<longleftrightarrow> fBex (finite_native_definition_readings E (fst d) (snd d))
      (\<lambda>(p,F). fBex F (\<lambda>(c,S). f |\<in>| finite_schema_dependencies S))"
    by (auto simp: finite_native_definition_edges_member rows)
  then show ?thesis unfolding finite_native_definition_edges_correct[symmetric] by blast
qed

definition finite_edge_argument_read :: "finite_factor_term \<Rightarrow> (local_address option finite_artifact_environment\<times>
    (local_address option definition_site\<times>local_address option definition_site)) option" where
  "finite_edge_argument_read=finite_pair_read finite_environment_value_read
    (finite_pair_read finite_site_value_read finite_site_value_read)"

theorem finite_edge_argument_read_exact:
  "finite_edge_argument_read t=Some (E,(d,f)) \<longleftrightarrow> (\<exists>e.
    decode_finite_term t=Pair_Term e (Pair_Term (definition_site_value d) (definition_site_value f)) \<and>
    environment_value_presents (decode_finite_environment E) e)"
proof -
  have site: "finite_site_value_read v=Some x \<longleftrightarrow> decode_finite_term v=definition_site_value x" for v x
    by (cases x) (simp only: finite_site_value_read_exact fst_conv snd_conv)
  have sites: "finite_pair_read finite_site_value_read finite_site_value_read v=Some y \<longleftrightarrow>
      decode_finite_term v=Pair_Term (definition_site_value (fst y)) (definition_site_value (snd y))" for v y
  proof -
    obtain a b where y: "y=(a,b)" by (cases y)
    show ?thesis
      by (simp add: y finite_pair_read_present[where P="\<lambda>x w. w=definition_site_value x"
        and Q="\<lambda>x w. w=definition_site_value x", OF site site])
  qed
  show ?thesis
    by (auto simp: finite_edge_argument_read_def finite_pair_read_present[where
      P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
      and Q="\<lambda>y w. w=Pair_Term (definition_site_value (fst y)) (definition_site_value (snd y))",
      OF finite_environment_value_read_exact sites])
qed

definition finite_definition_edge_reading_decision :: "finite_factor_term \<Rightarrow> bool" where
  "finite_definition_edge_reading_decision t=(case finite_edge_argument_read t of None \<Rightarrow> False
    | Some (E,(d,f)) \<Rightarrow> fBex (finite_native_definition_readings E (fst d) (snd d))
        (\<lambda>(p,F). fBex F (\<lambda>(c,S). f |\<in>| finite_schema_dependencies S)))"

lemma finite_definition_edge_reading_decision_read:
  assumes "finite_edge_argument_read t=Some (E,(d,f))"
  shows "finite_definition_edge_reading_decision t \<longleftrightarrow> (d,f)\<in>native_definition_edges (decode_finite_environment E)"
  using assms by (simp only: finite_definition_edge_reading_decision_def option.case prod.case finite_definition_edges_at)

theorem finite_definition_edge_reading_decision_exact:
  "finite_definition_edge_reading_decision t \<longleftrightarrow> definition_edge_reading_result (decode_finite_term t)"
proof
  assume holds: "finite_definition_edge_reading_decision t"
  obtain E d f where read: "finite_edge_argument_read t=Some (E,(d,f))"
    using holds by (cases "finite_edge_argument_read t")
      (auto simp: finite_definition_edge_reading_decision_def split: prod.splits)
  have edge: "(d,f)\<in>native_definition_edges (decode_finite_environment E)"
    using holds by (simp only: finite_definition_edge_reading_decision_read[OF read])
  obtain e where "decode_finite_term t=Pair_Term e (Pair_Term (definition_site_value d) (definition_site_value f))"
      "environment_value_presents (decode_finite_environment E) e"
    using read by (auto simp: finite_edge_argument_read_exact)
  then show "definition_edge_reading_result (decode_finite_term t)" using edge by blast
next
  assume "definition_edge_reading_result (decode_finite_term t)"
  then obtain E e d f where z: "decode_finite_term t=Pair_Term e
      (Pair_Term (definition_site_value d) (definition_site_value f))"
    and pe: "environment_value_presents E e" and edge: "(d,f)\<in>native_definition_edges E"
    by blast
  obtain G where g: "decode_finite_environment G=E" by (rule environment_value_presents_finite[OF pe])
  have read: "finite_edge_argument_read t=Some (G,(d,f))"
    using z pe by (auto simp: finite_edge_argument_read_exact g)
  show "finite_definition_edge_reading_decision t"
    using edge by (simp only: finite_definition_edge_reading_decision_read[OF read] g)
qed

corollary finite_definition_edge_reading_decision_meaning:
  "finite_definition_edge_reading_decision t \<longleftrightarrow>
    (82,decode_finite_term t)\<in>positive_meaning definition_edge_reading_system"
  by (simp only: finite_definition_edge_reading_decision_exact definition_edge_reading_exact)

section \<open>Controls\<close>

text \<open>
  Over the equality program's artifact at the use @{term None} (@{const reader_control_environment}): its
  package at [0] holds one definition, at [1], with a variable interface and no callee; nothing is defined at
  [2]. 72 at the definition with a formed operand and with an unformed one (the octet 256), and at [2]; 81 at
  every row of the definition's clause family, at [1] and at [2]; 82 from the definition to itself (it calls
  nothing) and from [2]; each counterpart at a term of another shape. Each control is executed, and its
  relation's outcome follows beside it from the exactness above.
\<close>

abbreviation reader_control_citation :: "local_address \<Rightarrow> finite_factor_term \<Rightarrow> finite_factor_term" where
  "reader_control_citation r x\<equiv>Finite_Pair (Finite_Pair (finite_environment_value reader_control_environment)
    (finite_use_data None)) (Finite_Pair (Finite_Payload r) x)"

abbreviation reader_control_socket :: "local_address\<times>local_address \<Rightarrow> finite_factor_term" where
  "reader_control_socket z\<equiv>Finite_Pair (Finite_Payload (fst z)) (Finite_Payload (snd z))"

abbreviation reader_control_edge where
  "reader_control_edge d f\<equiv>Finite_Pair (finite_environment_value reader_control_environment)
    (Finite_Pair (finite_site_data d) (finite_site_data f))"

value "finite_clause_rows reader_control_environment None [1]"

lemma definition_reader_controls:
  "finite_definition_call_admission_decision (reader_control_citation [1] (Finite_Payload [])) \<and>
    \<not>finite_definition_call_admission_decision (reader_control_citation [1] (Finite_Payload [256])) \<and>
    \<not>finite_definition_call_admission_decision (reader_control_citation [2] (Finite_Payload [])) \<and>
    finite_clause_rows reader_control_environment None [1]\<noteq>{||} \<and>
    fBall (finite_clause_rows reader_control_environment None [1]) (\<lambda>z.
      finite_definition_clause_reading_decision (reader_control_citation [1] (reader_control_socket z)) \<and>
      \<not>finite_definition_clause_reading_decision (reader_control_citation [2] (reader_control_socket z))) \<and>
    \<not>finite_definition_edge_reading_decision (reader_control_edge (None,[1]) (None,[1])) \<and>
    \<not>finite_definition_edge_reading_decision (reader_control_edge (None,[2]) (None,[1])) \<and>
    \<not>finite_definition_call_admission_decision (Finite_Payload []) \<and>
    \<not>finite_definition_clause_reading_decision (Finite_Payload []) \<and>
    \<not>finite_definition_edge_reading_decision (Finite_Payload [])"
  by eval

lemma definition_reader_control_admitted:
  "finite_definition_call_admission_decision (reader_control_citation [1] (Finite_Payload []))"
  using definition_reader_controls by blast

lemma definition_reader_control_unformed:
  "\<not>finite_definition_call_admission_decision (reader_control_citation [1] (Finite_Payload [256]))"
  using definition_reader_controls by blast

lemma definition_reader_control_undefined:
  "\<not>finite_definition_call_admission_decision (reader_control_citation [2] (Finite_Payload []))"
  using definition_reader_controls by blast

lemma definition_reader_control_rows:
  assumes "z |\<in>| finite_clause_rows reader_control_environment None [1]"
  shows "finite_definition_clause_reading_decision (reader_control_citation [1] (reader_control_socket z))"
    "\<not>finite_definition_clause_reading_decision (reader_control_citation [2] (reader_control_socket z))"
  using definition_reader_controls assms by blast+

lemma definition_reader_control_edges:
  "\<not>finite_definition_edge_reading_decision (reader_control_edge (None,[1]) (None,[1]))"
  "\<not>finite_definition_edge_reading_decision (reader_control_edge (None,[2]) (None,[1]))"
  using definition_reader_controls by blast+

lemmas definition_reader_control_relations=
  definition_reader_control_admitted[unfolded finite_definition_call_admission_decision_meaning]
  definition_reader_control_unformed[unfolded finite_definition_call_admission_decision_meaning]
  definition_reader_control_undefined[unfolded finite_definition_call_admission_decision_meaning]
  definition_reader_control_rows[unfolded finite_definition_clause_reading_decision_meaning]
  definition_reader_control_edges[unfolded finite_definition_edge_reading_decision_meaning]

end
