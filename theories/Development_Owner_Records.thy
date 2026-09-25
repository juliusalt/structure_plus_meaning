theory Development_Owner_Records
  imports Development_Certified_Generations
begin

section \<open>A generation stands at the index of its own payload\<close>

text \<open>
  A generation the native loop records stands at a locus that is an index and nothing else: the
  whole-artifact target of its own payload's quotation, which no program reads but a snapshot's
  lookup. Recording at that index is the library's recording of a presented payload under the policy
  listing exactly it, with the locus supplied by the payload itself; every generation the first
  problem's route records (the owner records, the posing, the admitted answer, its verification) is
  recorded so.
\<close>

definition development_indexed_generation ::
    "finite_factor_term \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow> development_generation_row list \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_indexed_generation t H rows=Option.bind (development_data_target t)
     (\<lambda>l. development_payload_generation_with development_payload_judgment t H l rows)"

lemma development_indexed_generation_built:
  assumes built: "development_indexed_generation t H rows=Some (B,u,G)"
  obtains l where "development_data_target t=Some l"
    "development_payload_generation_with development_payload_judgment t H l rows=Some (B,u,G)"
  using built by (auto simp: development_indexed_generation_def bind_eq_Some_conv)

theorem development_indexed_generation_certified:
  assumes built: "development_indexed_generation t H rows=Some (B,u,G)"
  obtains R d K pu E root where "development_data_target t=Some (generation_payload G)"
    "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "generation_predecessors G=fset_of_list (map snd rows)"
    "finite_check_generation G B u []"
    "environment_included (decode_finite_environment H) (decode_finite_environment B)"
proof -
  obtain l where target: "development_data_target t=Some l"
    and recorded: "development_payload_generation_with development_payload_judgment t H l rows=Some (B,u,G)"
    by (rule development_indexed_generation_built[OF built])
  obtain R d K pu E root where payload: "development_data_target t=Some (generation_payload G)"
      "generation_payload G=Finite_Whole R"
      "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
      "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
        (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
      "generation_locus G=l" "generation_predecessors G=fset_of_list (map snd rows)"
      "finite_check_generation G B u []"
      "environment_included (decode_finite_environment H) (decode_finite_environment B)"
    by (rule development_payload_generation_certified[OF recorded])
  have locus: "generation_locus G=generation_payload G" using target payload(1,5) by simp
  show thesis by (rule that[OF payload(1) locus payload(2,3,4,6,7,8)])
qed

lemma development_indexed_generation_recorded:
  assumes built: "development_indexed_generation t H rows=Some (B,u,G)"
  shows "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
    "finite_generation_formed G"
proof -
  obtain l where recorded: "development_payload_generation_with development_payload_judgment t H l rows=Some (B,u,G)"
    by (rule development_indexed_generation_built[OF built])
  show "finite_environment_formed B" "finite_environment_included H B" "finite_check_generation G B u []"
    by (rule development_payload_generation_recorded[OF recorded])+
  show "finite_generation_formed G" by (rule development_payload_generation_fields(2)[OF recorded])
qed

section \<open>A base generation stands at the index of its payload in an environment of its own\<close>

text \<open>
  A base generation is the indexed generation recorded in the empty environment with no predecessor: its locus
  is its payload and it has no predecessor. The owner records and the native state's first generation are its
  instances.
\<close>

definition development_base_generation ::
    "finite_factor_term \<Rightarrow> (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_base_generation t=development_indexed_generation t (finite_enumerated_environment [] []) []"

theorem development_base_generation_certified:
  assumes built: "development_base_generation t=Some (B,u,G)"
  obtains R d K pu E root where "development_data_target t=Some (generation_payload G)"
    "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R" "generation_predecessors G={||}"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "finite_check_generation G B u []"
proof -
  have indexed: "development_indexed_generation t (finite_enumerated_environment [] []) []=Some (B,u,G)"
    using built by (simp only: development_base_generation_def)
  obtain R d K pu E root where certified: "development_data_target t=Some (generation_payload G)"
      "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
      "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
      "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
        (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
      "generation_predecessors G=fset_of_list (map snd ([]::development_generation_row list))"
      "finite_check_generation G B u []"
      "environment_included (decode_finite_environment (finite_enumerated_environment [] [])) (decode_finite_environment B)"
    by (rule development_indexed_generation_certified[OF indexed])
  have base: "generation_predecessors G={||}" using certified(6) by simp
  show thesis by (rule that[OF certified(1,2,3) base certified(4,5,7)])
qed

lemmas development_base_generation_recorded=
  development_indexed_generation_recorded[of t "finite_enumerated_environment [] []" "[]",
    folded development_base_generation_def] for t

section \<open>Owner records\<close>

text \<open>
  An owner record is a base generation, recorded in an environment of its own at the index of its
  payload, whose payload is the owner's words as the owner ledger holds them: the entry's stamp, its
  addressee line and the quoted words, one inert payload of their octets that no program reads as
  structure. The certificate of its cause establishes that the policy lists the payload and nothing
  about the words being the owner's: the transcription is generated, made outside the loop from the
  ledger, and a residual. No record cites another; an order between the owner's words is the ledger's.
\<close>

definition owner_ledger_octets :: "string \<Rightarrow> octets" where
  "owner_ledger_octets s=map of_char s"

definition development_owner_record ::
    "finite_factor_term \<Rightarrow> (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_owner_record=development_base_generation"

lemmas development_owner_record_certified=development_base_generation_certified[folded development_owner_record_def]

text \<open>The directions of 2026-09-24 that pose the native loop's first problem, transcribed.\<close>

definition development_owner_direction_1750 :: finite_factor_term where
  \<open>development_owner_direction_1750=Finite_Payload (
    owner_ledger_octets ''**2026-09-24 17:50** (to plan-56 (planner); recorded by the harness):'' @
    [10,10] @
    owner_ledger_octets ''> Upon further review of the current state of the repository, I found that theere is no native definition of the notion of a problem - yet there are questions like the one that I just answered and notions like readiness that depend on what a problem is - how is this possible? Clearly to even be able to do anything in the loop the most fundamental thing that needs to be done is the development of a native notion of a problem is it not? This seems like a fundamental flaw to everything that was done and is being done so far that needs to be adressed.'')\<close>

definition development_owner_direction_1812 :: finite_factor_term where
  \<open>development_owner_direction_1812=Finite_Payload (
    owner_ledger_octets ''**2026-09-24 18:12** (to plan-56 (planner); recorded by the harness):'' @
    [10,10] @
    owner_ledger_octets ''> Task 9 made problems structural, but as a way to present them without octets, not'' @
    [10] @
    owner_ledger_octets ''>   as a native definition - how is this have anything to do with what I wanted? Using structure rather than octets was meant to remove opaqueness instead it seems that all it did is move it from octets to structure. Every distinction a native program relies on must come from a native notion, not from a HOL presentation relation.'')\<close>

definition development_owner_direction_1836 :: finite_factor_term where
  \<open>development_owner_direction_1836=Finite_Payload (
    owner_ledger_octets ''**2026-09-24 18:36** (to plan-57 (planner); recorded by the harness):'' @
    [10,10] @
    owner_ledger_octets ''> Does design #373 not contradict what I just said at its core: "a problem is a row '' @
    [226,128,166] @
    owner_ledger_octets '' at a locus", its subject "the key", justified by "a row is native structure already"'')\<close>

definition development_owner_direction_1853 :: finite_factor_term where
  \<open>development_owner_direction_1853=Finite_Payload (
    owner_ledger_octets ''**2026-09-24 18:53** (to plan-57 (planner); recorded by the harness):'' @
    [10,10] @
    owner_ledger_octets ''> Now that I think about it the problem of "what is a problem" should be the first problem tackled the native loop and then the problem I gave for Q2 which would then excercise the quality of the produced solution.'')\<close>

definition development_owner_direction_1957 :: finite_factor_term where
  \<open>development_owner_direction_1957=Finite_Payload (
    owner_ledger_octets ''**2026-09-24 19:57** (to the monitoring session, on Q23 (a), for the planner; recorded by the monitoring session):'' @
    [10,10] @
    owner_ledger_octets ''> Q23(a), to use this test and not only the octet audit. If you want that, say so on Q23 - ok tells that I endorce this to the planner.'')\<close>

text \<open>
  The length and octet sum of each transcription, as the ledger's bytes give them: a check of the
  transcription against the ledger, not a reading of the words.
\<close>

lemma development_owner_directions_transcribed:
  "map (\<lambda>t. case t of Finite_Payload v \<Rightarrow> (length v,sum_list v) | _ \<Rightarrow> (0,0))
    [development_owner_direction_1750,development_owner_direction_1812,development_owner_direction_1836,
     development_owner_direction_1853,development_owner_direction_1957]=
   [(624,56124),(486,43599),(243,20502),(285,24780),(251,21023)]"
  by eval

definition development_owner_record_1750 where
  "development_owner_record_1750=development_owner_record development_owner_direction_1750"
definition development_owner_record_1812 where
  "development_owner_record_1812=development_owner_record development_owner_direction_1812"
definition development_owner_record_1836 where
  "development_owner_record_1836=development_owner_record development_owner_direction_1836"
definition development_owner_record_1853 where
  "development_owner_record_1853=development_owner_record development_owner_direction_1853"
definition development_owner_record_1957 where
  "development_owner_record_1957=development_owner_record development_owner_direction_1957"

text \<open>
  A record reads back when the payload its generation carries is the quotation of the transcription,
  the locus is that payload, and it has no predecessor.
\<close>

definition development_owner_record_read_back ::
    "finite_factor_term \<Rightarrow> (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option \<Rightarrow>
      bool option" where
  "development_owner_record_read_back t r=map_option (\<lambda>(B,u,G). development_data_target t=Some (generation_payload G) \<and>
     generation_locus G=generation_payload G \<and> generation_predecessors G={||}) r"

section \<open>The form of the owner's approval\<close>

text \<open>
  The owner's approval of a generation is an owner record citing it: recorded in the environment of the
  cited generation's row, that row its only predecessor. The approval is no premise of a native
  relation; it is the adoption of what it cites. No approval is recorded here.
\<close>

definition development_owner_approval ::
    "finite_factor_term \<Rightarrow> local_address option finite_artifact_environment \<Rightarrow> development_generation_row \<Rightarrow>
      (local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_owner_approval t H row=development_indexed_generation t H [row]"

theorem development_owner_approval_certified:
  assumes built: "development_owner_approval t H (s,A)=Some (B,u,G)"
    and cited: "finite_check_generation A H (fst s) (snd s)"
  obtains R d K pu E root where "generation_predecessors G={|A|}" "finite_check_generation A B (fst s) (snd s)"
    "development_data_target t=Some (generation_payload G)"
    "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
    "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
    "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
      (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
    "finite_check_generation G B u []"
proof -
  have indexed: "development_indexed_generation t H [(s,A)]=Some (B,u,G)"
    using built by (simp only: development_owner_approval_def)
  note recorded=development_indexed_generation_recorded[OF indexed]
  have "list_all (\<lambda>(d,G). finite_check_generation G B (fst d) (snd d)) [(s,A)]"
    by (rule development_rows_carried[OF _ recorded(2) recorded(1)]) (simp add: cited)
  then have carried: "finite_check_generation A B (fst s) (snd s)" by simp
  obtain R d K pu E root where certified: "development_data_target t=Some (generation_payload G)"
      "generation_locus G=generation_payload G" "generation_payload G=Finite_Whole R"
      "development_policy_source_with [Finite_Target (Finite_Whole R)]=Some (d,K,pu)"
      "certified_policy_cause_at (decode_finite_environment K) pu [] d (decode_finite_environment B) u []
        (decode_finite_generation G) (decode_finite_environment E) root (decode_finite_object R)"
      "generation_predecessors G=fset_of_list (map snd [(s,A)])"
      "finite_check_generation G B u []"
      "environment_included (decode_finite_environment H) (decode_finite_environment B)"
    by (rule development_indexed_generation_certified[OF indexed])
  have cites: "generation_predecessors G={|A|}" using certified(6) by simp
  show thesis by (rule that[OF cites carried certified(1,2,3,4,5,7)])
qed

section \<open>The five records, executed\<close>

ML \<open>
  fun development_owner_record_timed ctxt stamp =
    let
      val t = Syntax.read_term ctxt ("development_owner_record_read_back development_owner_direction_" ^ stamp ^
        " development_owner_record_" ^ stamp)
      val timing = Timing.start ()
      val r = Value_Command.value ctxt t
      val elapsed = #elapsed (Timing.result timing)
    in writeln ("OWNER RECORD " ^ stamp ^ ": " ^ Syntax.string_of_term ctxt r ^ " in " ^ Time.toString elapsed ^ " s") end
\<close>

ML_val \<open>development_owner_record_timed \<^context> "1750"\<close>
ML_val \<open>development_owner_record_timed \<^context> "1812"\<close>
ML_val \<open>development_owner_record_timed \<^context> "1836"\<close>
ML_val \<open>development_owner_record_timed \<^context> "1853"\<close>
ML_val \<open>development_owner_record_timed \<^context> "1957"\<close>

end
