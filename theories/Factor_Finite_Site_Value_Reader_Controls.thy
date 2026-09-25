theory Factor_Finite_Site_Value_Reader_Controls
  imports Factor_Finite_Site_Value_Readers Criticism_Octet_Samples Factor_Stated_Leaves
begin

text \<open>
  The executed controls of the readers over an environment value, of the evaluation above an implemented
  base (E1), of the criticism's samples (S1 and the octet sample) and of the stated-leaves reader. No
  library theory imports them: a library theory on the route runs no evaluation.
\<close>

section \<open>Controls of the readers over an environment value\<close>

text \<open>
  Two environments: the empty one (@{const finite_empty_environment}), and one holding a single artifact at the
  use @{term None} whose carrier is the empty address alone, with no incidence and no data. Each reader is
  executed at a presented and at a malformed or refused term, and its presentation relation's outcome follows
  beside it from the reader's exactness: a reading states the presentation, an absent reading refuses it for
  every value.
\<close>

definition environment_reader_control_artifact :: finite_exact_artifact where
  "environment_reader_control_artifact=\<lparr>finite_structure=\<lparr>finite_carrier={|[]|},finite_incidence={||}\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings={||}\<rparr>\<rparr>"

definition environment_reader_control_rooted :: "local_address option finite_artifact_environment" where
  "environment_reader_control_rooted=\<lparr>finite_environment_artifacts={|(None,environment_reader_control_artifact)|},
    finite_environment_bindings={||}\<rparr>"

abbreviation environment_pair_read_control_term where
  "environment_pair_read_control_term\<equiv>
    Finite_Pair (finite_environment_value finite_empty_environment) (finite_environment_value environment_reader_control_rooted)"

abbreviation environment_pair_read_control_malformed_term where
  "environment_pair_read_control_malformed_term\<equiv>
    Finite_Pair (finite_environment_value finite_empty_environment) (Finite_Payload [1])"

abbreviation source_root_read_control_term where
  "source_root_read_control_term\<equiv>
    Finite_Pair (Finite_Pair (finite_environment_value environment_reader_control_rooted) (Finite_Payload [])) (Finite_Payload [])"

abbreviation source_root_read_control_malformed_term where
  "source_root_read_control_malformed_term\<equiv>
    Finite_Pair (Finite_Pair (finite_environment_value environment_reader_control_rooted) (Finite_Payload [1])) (Finite_Payload [])"

subsection \<open>The pair of environment values\<close>

lemma environment_pair_read_control:
  "finite_environment_pair_read environment_pair_read_control_term=
    Some (finite_empty_environment,environment_reader_control_rooted)"
  by eval

lemmas environment_pair_read_control_presents=
  environment_pair_read_control[unfolded finite_environment_pair_read_exact]

lemma environment_pair_read_control_malformed:
  "finite_environment_pair_read environment_pair_read_control_malformed_term=None"
  by eval

lemma environment_pair_read_control_malformed_refused:
  "\<not>(\<exists>e f. decode_finite_term environment_pair_read_control_malformed_term=Pair_Term e f \<and>
    environment_value_presents (decode_finite_environment E) e \<and>
    environment_value_presents (decode_finite_environment F) f)"
  by (metis finite_environment_pair_read_exact environment_pair_read_control_malformed option.distinct(1))

subsection \<open>The source-root argument\<close>

lemma source_root_read_control:
  "finite_source_root_read source_root_read_control_term=Some ((environment_reader_control_rooted,None),[])"
  by eval

lemmas source_root_read_control_presents=
  source_root_read_control[unfolded finite_source_root_read_exact]

lemma source_root_read_control_malformed:
  "finite_source_root_read source_root_read_control_malformed_term=None"
  by eval

lemma source_root_read_control_malformed_refused:
  "\<not>(\<exists>e. decode_finite_term source_root_read_control_malformed_term=
      source_root_argument e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents (decode_finite_environment E) e)"
  by (metis finite_source_root_read_exact source_root_read_control_malformed option.distinct(1))

subsection \<open>The site value\<close>

text \<open>
  The site value presented at the rooted environment's one position is read back as that environment and site;
  the value presented at the address [1], outside the artifact's carrier and so no position of the environment,
  is read as nothing, and no environment and site are presented by it.
\<close>

lemma site_read_control:
  "finite_site_read (finite_site_presented environment_reader_control_rooted None [])=
    Some (environment_reader_control_rooted,None,[])"
  by eval

lemmas site_read_control_presents=site_read_control[unfolded finite_site_read_exact]

lemma site_read_control_outside:
  "finite_site_read (finite_site_presented environment_reader_control_rooted None [1])=None"
  by eval

lemma site_read_control_outside_refused:
  "\<not>site_value_presents (decode_finite_environment E) u r
    (decode_finite_term (finite_site_presented environment_reader_control_rooted None [1]))"
  by (metis finite_site_read_exact site_read_control_outside option.distinct(1))

section \<open>A fixture: the whole target of the empty artifact\<close>

text \<open>
  The octet sample's controls and the stated-leaves reader's controls state one pattern, the whole target
  of the empty artifact, at their two variable types.
\<close>

definition control_empty_target :: "'a finite_term_pattern" where
  "control_empty_target=Finite_Pattern_Target (Finite_Whole finite_empty_artifact)"

section \<open>The programs of the native evaluator's controls\<close>

subsection \<open>E1: a premise-only witness answered above a base\<close>

text \<open>
  Three sites over the variable interface: the leaf holds of every term, the witness holds of a term when
  the leaf holds of some term (a premise-only variable), and the root holds of a term when the witness
  does. The plain evaluator has no answer at the root's demand; above the base holding the witness, whose
  decision is that its argument is formed, the demand is answered, and the decision is proved exact at the
  demanded witness call from the program's own positive meaning.
\<close>

definition implemented_base_control :: "local_address option finite_native_system" where
  "implemented_base_control=\<lparr>finite_system_interfaces=
      {|((None,[1]),Finite_Variable [0]),((None,[2]),Finite_Variable [0]),((None,[3]),Finite_Variable [0])|},
    finite_system_clauses={|
      (((None,[1]),[0]),\<lparr>finite_schema_conclusion=Finite_Variable [0],finite_schema_premises={||},
        finite_schema_materials={||}\<rparr>),
      (((None,[2]),[0]),\<lparr>finite_schema_conclusion=Finite_Variable [0],
        finite_schema_premises={|([0],((None,[1]),Finite_Variable [1]))|},finite_schema_materials={||}\<rparr>),
      (((None,[3]),[0]),\<lparr>finite_schema_conclusion=Finite_Variable [0],
        finite_schema_premises={|([0],((None,[2]),Finite_Variable [0]))|},finite_schema_materials={||}\<rparr>)|}\<rparr>"

definition implemented_base_control_decision ::
    "local_address option definition_site\<times>finite_factor_term \<Rightarrow> bool" where
  "implemented_base_control_decision q=finite_term_formed (snd q)"

definition implemented_base_control_demand ::
    "(local_address option definition_site\<times>finite_factor_term) fset" where
  "implemented_base_control_demand={|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|}"

subsection \<open>S1: the criticism's sample\<close>

text \<open>
  Two artifacts at two uses: the canonical environment value lists the row of the first use first, the
  reversed one the row of the second. One entry reads the first artifact row literally, and the sample
  records a row at its pair; one entry asks for two artifact rows, invariant over every enumeration, and
  records none. A program whose rule calls an undefined site has no evaluation, and a program whose entry
  holds nowhere has an empty table.
\<close>

definition control_environment :: "local_address option finite_artifact_environment" where
  "control_environment=finite_enumerated_environment
    [(Some [0],finite_empty_artifact),(Some [1],finite_empty_artifact)] []"

definition control_first_row :: finite_factor_term where
  "control_first_row=(case finite_environment_value control_environment of
    Finite_Pair (Finite_Pair r x) y \<Rightarrow> r | t \<Rightarrow> t)"

definition control_first_entry :: "local_address option definition_site" where
  "control_first_entry=(Some [4,3,5],[0])"

definition control_invariant_entry :: "local_address option definition_site" where
  "control_invariant_entry=(Some [4,3,5],[1])"

definition control_missing_entry :: "local_address option definition_site" where
  "control_missing_entry=(Some [4,3,5],[2])"

definition control_program :: "local_address option finite_native_system" where
  "control_program=finite_rule_program
    [(control_first_entry,[([0],finite_native_rule (Finite_Pattern_Pair
        (Finite_Pattern_Pair (finite_exact_term_pattern control_first_row) (native_var 0)) (native_var 1)) [])]),
     (control_invariant_entry,[([0],finite_native_rule (Finite_Pattern_Pair
        (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3)) [])])]"

definition control_unavailable_program :: "local_address option finite_native_system" where
  "control_unavailable_program=finite_rule_program
    [(control_first_entry,[([0],finite_native_rule (native_var 0) [([0],(control_missing_entry,native_var 0))])])]"

definition control_empty_program :: "local_address option finite_native_system" where
  "control_empty_program=finite_rule_program
    [(control_first_entry,[([0],finite_native_rule (Finite_Pattern_Payload [7]) [])])]"

definition control_pairs :: "(finite_factor_term\<times>finite_factor_term) list" where
  "control_pairs=reversal_pairs Environment_Argument [control_environment]"

definition control_reading :: "unit \<Rightarrow> bool list" where
  "control_reading _=(let p=canonical_argument_value control_environment Environment_Argument;
      q=reversed_argument_value control_environment Environment_Argument;
      ds=[control_first_entry,control_invariant_entry] in
    case criticism_table control_program ds control_pairs of None \<Rightarrow> [False]
    | Some A \<Rightarrow> [p\<noteq>q,criticism_record ds control_pairs A={|(p,q,control_first_entry,())|},
        criticism_refuted ds control_pairs A={|control_first_entry|},
        (control_first_entry,p) |\<in>| A,(control_invariant_entry,p) |\<in>| A,(control_invariant_entry,q) |\<in>| A])"

definition control_unavailable :: "unit \<Rightarrow> bool list" where
  "control_unavailable _=[criticism_table control_unavailable_program [control_first_entry] control_pairs=None]"

definition control_empty :: "unit \<Rightarrow> bool list" where
  "control_empty _=[criticism_table control_empty_program [control_first_entry] control_pairs=Some {||}]"

text \<open>
  Over a base, E1's program: its root (None,[3]) holds of a term where the witness (None,[2]) does, and the
  witness's clause has the premise-only variable [1]. The sample calls the root at the empty payload and at
  a payload that is no octet list, so its two sides differ. The plain sample is unavailable, its diagnosis
  naming the witness's clause and variable; over the base holding the witness, whose decision is that the
  argument is formed, proved exact at the demand's base call, the table and its record stand beside the
  program's meaning.
\<close>

definition criticism_base_control_pairs :: "(finite_factor_term\<times>finite_factor_term) list" where
  "criticism_base_control_pairs=[(Finite_Payload [],Finite_Payload [256])]"

subsection \<open>The octet sample\<close>

text \<open>
  One program with two entries. The first holds of a payload exactly when it is the address of the one
  atom of a stated target literal, observed by a material premise: the octet is read only through the
  target, not stated as a payload, so the sample moves it and records a row, listing the premise. The
  second, observation-free, holds of a pair of equal terms and records none.
\<close>

definition octet_control_target :: finite_exact_artifact where
  "octet_control_target=finite_enumerated_artifact [[5]] [] [] []"

definition octet_moved_target :: finite_exact_artifact where
  "octet_moved_target=finite_enumerated_artifact [[7]] [] [] []"

definition octet_control_material :: "local_address finite_material_pattern" where
  "octet_control_material=\<lparr>finite_material_source=Finite_Pattern_Target (Finite_Whole octet_control_target),
    finite_material_atoms=Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 0)
      (Finite_Pattern_Target (Finite_Anchor octet_control_target [5]))) control_empty_target,
    finite_material_edges=control_empty_target, finite_material_counts=control_empty_target,
    finite_material_functions=control_empty_target\<rparr>"

definition octet_material_entry :: "local_address option definition_site" where
  "octet_material_entry=(Some [4,3,6],[0])"

definition octet_equality_entry :: "local_address option definition_site" where
  "octet_equality_entry=(Some [4,3,6],[1])"

definition octet_control_program :: "local_address option finite_native_system" where
  "octet_control_program=finite_rule_program
    [(octet_material_entry,[([0],(finite_native_rule (native_var 0) [])
        \<lparr>finite_schema_materials:={|([1],octet_control_material)|}\<rparr>)]),
     (octet_equality_entry,[([0],finite_native_rule (Finite_Pattern_Pair (native_var 0) (native_var 0)) [])])]"

definition octet_control_terms :: "finite_factor_term list" where
  "octet_control_terms=[Finite_Payload [5],Finite_Pair (Finite_Payload [5]) (Finite_Payload [5]),
    Finite_Pair (Finite_Payload [5]) (Finite_Payload [6]),
    Finite_Target (Finite_Whole octet_control_target),Finite_Target (Finite_Whole octet_moved_target)]"

definition octet_control_material_reading :: "unit \<Rightarrow> bool list" where
  "octet_control_material_reading _=(let P=octet_control_program; ts=octet_control_terms;
      ps=octet_sample_pairs P ts; p=Finite_Payload [5]; q=criticism_octet_sample P ts p in
    case criticism_table P [octet_material_entry] ps of None \<Rightarrow> [False]
    | Some A \<Rightarrow> [finite_system_payloads P={||},q\<noteq>p,
        criticism_record [octet_material_entry] ps A={|(p,q,octet_material_entry,())|},
        criticism_refuted [octet_material_entry] ps A={|octet_material_entry|},
        finite_entry_materials P octet_material_entry\<noteq>{||},
        octet_sample_rows P [octet_material_entry] ts=
          Some {|((p,q,octet_material_entry),finite_entry_materials P octet_material_entry)|},
        criticism_octet_sample P ts (Finite_Target (Finite_Whole octet_control_target))=
          Finite_Target (Finite_Whole octet_control_target),
        criticism_octet_sample P ts (Finite_Target (Finite_Whole octet_moved_target))\<noteq>
          Finite_Target (Finite_Whole octet_moved_target)])"

definition octet_control_equality_reading :: "unit \<Rightarrow> bool list" where
  "octet_control_equality_reading _=(let P=octet_control_program; ts=octet_control_terms;
      ps=octet_sample_pairs P ts in
    case criticism_table P [octet_equality_entry] ps of None \<Rightarrow> [False]
    | Some A \<Rightarrow> [finite_entry_materials P octet_equality_entry={||},
        criticism_record [octet_equality_entry] ps A={||},
        (octet_equality_entry,Finite_Pair (Finite_Payload [5]) (Finite_Payload [5])) |\<in>| A,
        (octet_equality_entry,criticism_octet_sample P ts (Finite_Pair (Finite_Payload [5]) (Finite_Payload [5]))) |\<in>| A])"

section \<open>One evaluation executes the native evaluator's controls\<close>

text \<open>
  One evaluation compiles the native evaluator once for all its controls: E1's (the plain evaluator, the
  evaluation above the base, the leaf's plain evaluation and the witness's admitted instance), S1's over
  the base, S1's plain controls and the octet sample's. Each part is named for the facts that read it.
\<close>

lemma native_evaluator_controls_executed:
  "(native_call_closure implemented_base_control {|((None,[3]),Finite_Payload [])|}=
      implemented_base_control_demand \<and>
    finite_program_evaluation implemented_base_control implemented_base_control_demand=None \<and>
    native_base_evaluation {|(None,[2])|} implemented_base_control_decision implemented_base_control
      {|((None,[3]),Finite_Payload [])|}=
      (implemented_base_control_demand,Some implemented_base_control_demand) \<and>
    finite_program_evaluation implemented_base_control {|((None,[1]),Finite_Payload [])|}=
      Some {|((None,[1]),Finite_Payload [])|} \<and>
    finite_admitted_schema_instance implemented_base_control (None,[2]) [0]
      {|([0],Finite_Payload []),([1],Finite_Payload [])|} (Finite_Payload [])
      {|([0],((None,[1]),Finite_Payload []))|}) \<and>
   (criticism_diagnosis {||} implemented_base_control [(None,[3])] criticism_base_control_pairs=
      (True,True,{|((None,[2]),[0],{|[1]|})|}) \<and>
    criticism_base_demand {|(None,[2])|} implemented_base_control [(None,[3])] criticism_base_control_pairs=
      {|((None,[3]),Finite_Payload []),((None,[3]),Finite_Payload [256]),((None,[2]),Finite_Payload [])|} \<and>
    criticism_base_table {|(None,[2])|} implemented_base_control_decision implemented_base_control [(None,[3])]
      criticism_base_control_pairs=Some {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|} \<and>
    criticism_record [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|}=
      {|(Finite_Payload [],Finite_Payload [256],(None,[3]),())|}) \<and>
   (control_reading ()=[True,True,True,True,True,True] \<and> control_unavailable ()=[True] \<and>
    control_empty ()=[True]) \<and>
   (octet_control_material_reading ()=[True,True,True,True,True,True,True,True] \<and>
    octet_control_equality_reading ()=[True,True,True,True])"
  by eval

lemmas implemented_base_control_executed=native_evaluator_controls_executed[THEN conjunct1]

lemmas criticism_base_control_executed=native_evaluator_controls_executed[THEN conjunct2, THEN conjunct1]

lemmas criticism_controls_executed=
  native_evaluator_controls_executed[THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemmas octet_controls_executed=
  native_evaluator_controls_executed[THEN conjunct2, THEN conjunct2, THEN conjunct2]

subsection \<open>E1's outcome\<close>

lemma implemented_base_control_plain:
  "native_call_evaluation implemented_base_control {|((None,[3]),Finite_Payload [])|}=
    (implemented_base_control_demand,None)"
  using implemented_base_control_executed by (simp add: native_call_evaluation_def)

lemmas implemented_base_control_answer=
  implemented_base_control_executed[THEN conjunct2, THEN conjunct2, THEN conjunct1]

lemma implemented_base_control_witness:
  "((None,[2]),Payload_Term [])\<in>positive_meaning (decode_finite_system implemented_base_control)"
proof -
  have leaf_evaluated: "finite_program_evaluation implemented_base_control {|((None,[1]),Finite_Payload [])|}=
      Some {|((None,[1]),Finite_Payload [])|}"
    using implemented_base_control_executed by blast
  have answered: "fset {|((None,[1]),Finite_Payload [])|}=
      {q\<in>fset {|((None,[1]),Finite_Payload [])|}.
        decode_finite_call_term q\<in>positive_meaning (decode_finite_system implemented_base_control)}"
    by (rule finite_program_evaluation_exact(2)[OF leaf_evaluated])
  have member: "((None,[1]),Finite_Payload [])\<in>fset {|((None,[1]),Finite_Payload [])|}" by simp
  have "decode_finite_call_term ((None,[1]),Finite_Payload [])\<in>
      positive_meaning (decode_finite_system implemented_base_control)"
  proof -
    have "((None,[1]),Finite_Payload [])\<in>{q\<in>fset {|((None,[1]),Finite_Payload [])|}.
        decode_finite_call_term q\<in>positive_meaning (decode_finite_system implemented_base_control)}"
      by (rule subst[where P="\<lambda>S. ((None,[1]),Finite_Payload [])\<in>S", OF answered member])
    then show ?thesis by blast
  qed
  then have leaf: "((None,[1]),Payload_Term [])\<in>positive_meaning (decode_finite_system implemented_base_control)"
    by (simp add: decode_finite_call_term_def)
  have admitted: "finite_admitted_schema_instance implemented_base_control (None,[2]) [0]
      {|([0],Finite_Payload []),([1],Finite_Payload [])|} (Finite_Payload [])
      {|([0],((None,[1]),Finite_Payload []))|}"
    using implemented_base_control_executed by blast
  have "((None,[2]),decode_finite_term (Finite_Payload []))\<in>
      positive_meaning (decode_finite_system implemented_base_control)"
    by (rule positive_meaning_step[OF admitted[unfolded finite_admitted_schema_instance_correct]])
      (use leaf in \<open>auto simp: decode_finite_premises_def decode_finite_call_term_def\<close>)
  then show ?thesis by simp
qed

lemma implemented_base_control_decision_exact:
  assumes "q |\<in>| implemented_base_control_demand" "fst q |\<in>| {|(None,[2])|}"
  shows "implemented_base_control_decision q \<longleftrightarrow>
    decode_finite_call_term q\<in>positive_meaning (decode_finite_system implemented_base_control)"
proof -
  have witness: "q=((None,[2]),Finite_Payload [])"
    using assms unfolding implemented_base_control_demand_def by auto
  show ?thesis using implemented_base_control_witness
    by (simp add: witness implemented_base_control_decision_def decode_finite_call_term_def octets_formed_def)
qed

theorem implemented_base_control_meaning:
  "fset implemented_base_control_demand=
    {q\<in>fset implemented_base_control_demand.
      decode_finite_call_term q\<in>positive_meaning (decode_finite_system implemented_base_control)}"
  by (rule native_base_evaluation_exact(2)[OF implemented_base_control_answer
    implemented_base_control_decision_exact])

subsection \<open>S1's outcome over a base\<close>

lemma criticism_base_control_plain:
  "criticism_table implemented_base_control [(None,[3])] criticism_base_control_pairs=None"
  using criticism_base_control_executed by (simp add: criticism_table_diagnosed)

lemma criticism_base_control_decided:
  "criticism_decision_exact {|(None,[2])|} implemented_base_control_decision implemented_base_control
    [(None,[3])] criticism_base_control_pairs"
  unfolding criticism_decision_exact_def
proof (intro allI impI)
  fix q
  assume demand: "q |\<in>| criticism_base_demand {|(None,[2])|} implemented_base_control [(None,[3])]
      criticism_base_control_pairs"
    and base: "fst q |\<in>| {|(None,[2])|}"
  have demanded: "criticism_base_demand {|(None,[2])|} implemented_base_control [(None,[3])]
      criticism_base_control_pairs=
      {|((None,[3]),Finite_Payload []),((None,[3]),Finite_Payload [256]),((None,[2]),Finite_Payload [])|}"
    using criticism_base_control_executed by blast
  have witness: "q=((None,[2]),Finite_Payload [])"
    using demand base unfolding demanded by auto
  show "implemented_base_control_decision q \<longleftrightarrow>
      decode_finite_call_term q\<in>positive_meaning (decode_finite_system implemented_base_control)"
    using implemented_base_control_witness
    by (simp add: witness implemented_base_control_decision_def decode_finite_call_term_def octets_formed_def)
qed

theorem criticism_base_control_meaning:
  "((None,[3]),Payload_Term [])\<in>positive_meaning (decode_finite_system implemented_base_control)"
  "((None,[3]),Payload_Term [256])\<notin>positive_meaning (decode_finite_system implemented_base_control)"
  "(c,c',d,w) |\<in>| criticism_record [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|} \<longleftrightarrow>
    criticism_paired criticism_base_control_pairs c c' \<and> d\<in>set [(None,[3])] \<and>
    (d,decode_finite_term c)\<in>positive_meaning (decode_finite_system implemented_base_control) \<and>
    (d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system implemented_base_control)"
proof -
  have table: "criticism_base_table {|(None,[2])|} implemented_base_control_decision implemented_base_control
      [(None,[3])] criticism_base_control_pairs=Some {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|}"
    using criticism_base_control_executed by blast
  have exact: "criticism_exact_table implemented_base_control [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|}"
    by (rule criticism_base_table_exact_table[OF table criticism_base_control_decided])
  have calls: "((None,[3]),Finite_Payload []) |\<in>| criticism_calls [(None,[3])] criticism_base_control_pairs"
    "((None,[3]),Finite_Payload [256]) |\<in>| criticism_calls [(None,[3])] criticism_base_control_pairs"
    by (simp_all add: criticism_calls_member criticism_sides_def criticism_base_control_pairs_def)
  show "((None,[3]),Payload_Term [])\<in>positive_meaning (decode_finite_system implemented_base_control)"
    using criticism_exact_tableD[OF exact calls(1)] by (simp add: decode_finite_call_term_def)
  show "((None,[3]),Payload_Term [256])\<notin>positive_meaning (decode_finite_system implemented_base_control)"
    using criticism_exact_tableD[OF exact calls(2)] by (simp add: decode_finite_call_term_def)
  show "(c,c',d,w) |\<in>| criticism_record [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|} \<longleftrightarrow>
    criticism_paired criticism_base_control_pairs c c' \<and> d\<in>set [(None,[3])] \<and>
    (d,decode_finite_term c)\<in>positive_meaning (decode_finite_system implemented_base_control) \<and>
    (d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system implemented_base_control)"
    by (rule exact_table_record_meaning[OF exact])
qed

section \<open>The stated-leaves reader's controls\<close>

text \<open>
  The reader holds clauses without head coverage (@{text Factor_Stated_Leaves}), so its controls are
  evaluated through the finite computation, exact against the leaves and so against the native contract,
  beside the audit's HOL counterpart at the same definitions: a program family of its own, compiled once.
\<close>

definition stated_leaves_controls :: "(nat finite_term_pattern\<times>(nat\<times>(nat,nat,nat) finite_factor_schema) fset) list" where
  "stated_leaves_controls=[
    (Finite_Variable 0,{|(0,\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Pattern_Payload [1]) control_empty_target,
      finite_schema_premises={||},finite_schema_materials={||}\<rparr>)|}),
    (Finite_Pattern_Pair (Finite_Variable 0) control_empty_target,
     {|(0,\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) control_empty_target,
      finite_schema_premises={|(1,(5,Finite_Pattern_Pair control_empty_target (Finite_Variable 0)))|},
      finite_schema_materials={|(2,\<lparr>finite_material_source=control_empty_target,finite_material_atoms=Finite_Variable 1,
        finite_material_edges=Finite_Variable 2,finite_material_counts=Finite_Variable 3,
        finite_material_functions=Finite_Variable 4\<rparr>)|}\<rparr>)|}),
    (Finite_Variable 0,{|(0,\<lparr>finite_schema_conclusion=Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Payload []),
      finite_schema_premises={|(1,(5,Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Variable 0)))|},
      finite_schema_materials={||}\<rparr>)|}),
    (Finite_Variable 0,{|(0,\<lparr>finite_schema_conclusion=Finite_Variable 0,
      finite_schema_premises={|(1,(5,Finite_Variable 0))|},finite_schema_materials={||}\<rparr>)|})]"

definition stated_leaves_control_reports where
  "stated_leaves_control_reports=map (\<lambda>(p,C). (finite_definition_stated p C,finite_definition_payloads p C))
    stated_leaves_controls"

ML \<open>
  val stated_leaves_control_context = @{context};
  val (stated_leaves_control_time, stated_leaves_control_value) =
    Timing.timing (Code_Evaluation.dynamic_value_strict stated_leaves_control_context)
      @{term "stated_leaves_control_reports"};
  val _ = writeln ("STATED_LEAVES_CONTROLS " ^ Timing.message stated_leaves_control_time);
  val _ = writeln (Syntax.string_of_term stated_leaves_control_context stated_leaves_control_value);
\<close>

end
