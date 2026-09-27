theory Factor_Input_Production_Controls
  imports Factor_Input_Productions Factor_Resolution_Modes Factor_Resolution_Controls
begin

text \<open>
  The input production's control (I2 of correction (13) of DECISIONS.md, task 495's entry, "Committed choice, for
  refusals"), one lemma proved by one evaluation; no library theory imports this theory.

  A lookup of a small artifact through an environment of two rows, as 37 through 12, in a small program whose sites 12
  and 37 hold 12's and 37's own clauses (@{const identity_socket_schema}, @{const lookup_socket_schema}). Site 26 admits
  any pair; 5 selects a row (u,a) of a list, returning the rest, 5((u,a),(rows,rest)); 1 inserts an element into a list,
  1(e,(l,l')) with l' the list l without one occurrence of e; 2 compares two lists as bags, 2((e,r),l) :- 2(r,l'),
  1(e,(l,l')), whose answers at a list are its permutations; 7(x,y) :- 2(x,y), the artifact comparison; 11 admits a
  list; 40, root((e,w),u) :- 37((e,w),(u,a)), calls 37 with its output free. 37 is declared a producer at
  @{const lookup_view}, and the socket 37.0/2 (12 at @{const view_identity}, frame {3}) declares
  @{const identity_input_registration}, class every answer. Selection is O4's moded one, 5 at its row view, so 5 binds
  12's input before 12 is taken, as at 37.0/1 in the given.

  The production's value at 12's clause is the stored artifact itself. The true call root(rows,[5]) is resolved with
  one certificate by the narrowed commitment with the production, 12 committed at the produced state and its
  sub-search a check; R5's committed search without the production resolves it too, keeping 37's least presentation
  after enumerating the stored artifact's permutations, in more states. The false call root(rows,[7]), whose use no row
  holds, is refuted, and the lookup of a presentation of another artifact, 37's output ground, is refuted with no
  production met; R4 refutes both and resolves the true call, its values beside.

  The control of an open sibling (OS2 of correction (15)): the same program with 26's clause replaced by
  26(x,y) :- 2(x,x) (@{text open_sibling_admission}, @{text open_sibling_program}), so that 37's sibling at socket 0
  is expanded and its bag comparison's goals, at two alternatives each, are pending under it when 12 is taken at
  37.0/2. None of them holds a variable 37's node binds at 12's premise or at the frame {3}, so the framed test
  commits the socket with the sibling open and the production is met: the true call is resolved in 30 states against
  58 without the production, one certificate each, and the false call is refuted in 6; R4 gives the same verdicts.
\<close>

definition input_control_root :: "(nat,nat,nat) finite_factor_schema" where
  "input_control_root = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 2),
    finite_schema_premises = {|(0,37,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
    finite_schema_materials = {||}\<rparr>"

definition input_control_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "input_control_program = \<lparr>finite_system_interfaces = fset_of_list (map (\<lambda>d. (d,Finite_Variable 0)) [1,2,5,7,11,12,26,37,40]),
    finite_system_clauses = {|((1,0),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1)) (Finite_Variable 1)),
      finite_schema_premises = {||}, finite_schema_materials = {||}\<rparr>),
    ((1,1),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 2))
          (Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))),
      finite_schema_premises = {|(0,1,Finite_Pattern_Pair (Finite_Variable 0)
        (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
      finite_schema_materials = {||}\<rparr>),
    ((2,0),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Pattern_Payload []) (Finite_Pattern_Payload []),
      finite_schema_premises = {||}, finite_schema_materials = {||}\<rparr>),
    ((2,1),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Variable 2),
      finite_schema_premises = {|(0,2,Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3)),
        (1,1,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)))|},
      finite_schema_materials = {||}\<rparr>),
    ((5,0),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
          (Finite_Variable 2)) (Finite_Variable 2)),
      finite_schema_premises = {||}, finite_schema_materials = {||}\<rparr>),
    ((5,1),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))
          (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 4))),
      finite_schema_premises = {|(0,5,Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
        (Finite_Pattern_Pair (Finite_Variable 3) (Finite_Variable 4)))|},
      finite_schema_materials = {||}\<rparr>),
    ((7,0),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
      finite_schema_premises = {|(0,2,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))|},
      finite_schema_materials = {||}\<rparr>),
    ((11,0),\<lparr>finite_schema_conclusion = Finite_Pattern_Payload [],
      finite_schema_premises = {||}, finite_schema_materials = {||}\<rparr>),
    ((11,1),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
      finite_schema_premises = {|(0,11,Finite_Variable 1)|}, finite_schema_materials = {||}\<rparr>),
    ((12,0),identity_socket_schema),
    ((26,0),\<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
      finite_schema_premises = {||}, finite_schema_materials = {||}\<rparr>),
    ((37,0),lookup_socket_schema),
    ((40,0),input_control_root)|}\<rparr>"

definition input_control_declarations :: "(nat,nat,nat,nat) produced_declarations" where
  "input_control_declarations = produced (narrowed \<lparr>declared_producers = {|(37,lookup_view,[snd (snd lookup_view)])|},
      declared_consumers = {||}, declared_sockets = {|(37,lookup_socket_schema,2,False,view_identity,lookup_view)|}\<rparr>
      (\<lambda>_ _ _ _. True))
    (\<lambda>e S s. if e = 37 \<and> s = 2 then Some identity_input_registration else None)"

definition input_control_row_view :: "nat resolution_view" where
  "input_control_row_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2), Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))"

definition input_control_modes :: "nat resolution_modes" where
  "input_control_modes = {|(5,input_control_row_view)|}"

fun input_control_data :: "finite_factor_term list \<Rightarrow> finite_factor_term" where
  "input_control_data [] = Finite_Payload []"
| "input_control_data (e # es) = Finite_Pair e (input_control_data es)"

definition input_control_artifact :: finite_factor_term where
  "input_control_artifact = input_control_data [Finite_Payload [1],Finite_Payload [2],Finite_Payload [3]]"

definition input_control_environment :: finite_factor_term where
  "input_control_environment = input_control_data
    [Finite_Pair (Finite_Payload [5]) input_control_artifact,
     Finite_Pair (Finite_Payload [6]) (input_control_data [Finite_Payload [4]])]"

definition input_control_call :: "octets \<Rightarrow> finite_factor_term" where
  "input_control_call u = Finite_Pair (Finite_Pair input_control_environment (Finite_Payload [])) (Finite_Payload u)"

definition input_control_lookup :: "finite_factor_term list \<Rightarrow> finite_factor_term" where
  "input_control_lookup a = Finite_Pair (Finite_Pair input_control_environment (Finite_Payload []))
    (Finite_Pair (Finite_Payload [5]) (input_control_data a))"

abbreviation input_control_produced :: "(nat,nat,nat,nat) resolution_commitment" where
  "input_control_produced \<equiv> finite_narrowed_commitment input_control_program 0 input_control_declarations lookup_frames"

abbreviation input_control_committed :: "(nat,nat,nat,nat) resolution_commitment" where
  "input_control_committed \<equiv> finite_framed_commitment (resolution_declarations.truncate input_control_declarations) lookup_frames"

definition input_control_run :: "(nat,nat,nat,nat) finite_schema_system \<Rightarrow>
    (nat,nat,nat,nat) resolution_commitment \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option \<times> nat \<times> nat" where
  "input_control_run P K d t n = (finite_resolution_verdict (finite_moded_resolution no_witness_construction K
      (resolution_declarations.truncate input_control_declarations) input_control_modes P d t n),
    commitment_certificates (finite_moded_resolution no_witness_construction K
      (resolution_declarations.truncate input_control_declarations) input_control_modes P d t n),
    committed_resolution_states (finite_moded_select no_witness_construction K
      (resolution_declarations.truncate input_control_declarations) input_control_modes P)
      no_witness_construction K P d t n)"

definition input_control_row ::
    "(nat,nat,nat,nat) resolution_commitment \<Rightarrow> nat \<Rightarrow> finite_factor_term \<Rightarrow> nat \<Rightarrow> bool option \<times> nat \<times> nat" where
  "input_control_row = input_control_run input_control_program"

abbreviation input_control_plain :: "nat \<Rightarrow> finite_factor_term \<Rightarrow> bool option" where
  "input_control_plain d t \<equiv> finite_resolution_verdict (finite_program_resolution no_witness_construction
    input_control_program d t 30)"

definition open_sibling_admission :: "(nat,nat,nat) finite_factor_schema" where
  "open_sibling_admission = \<lparr>finite_schema_conclusion = Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),
    finite_schema_premises = {|(0,2,Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 0))|},
    finite_schema_materials = {||}\<rparr>"

definition open_sibling_program :: "(nat,nat,nat,nat) finite_schema_system" where
  "open_sibling_program = input_control_program\<lparr>finite_system_clauses :=
    finsert ((26,0),open_sibling_admission)
      (ffilter (\<lambda>((d,c),S). d \<noteq> 26) (finite_system_clauses input_control_program))\<rparr>"

abbreviation open_sibling_produced :: "(nat,nat,nat,nat) resolution_commitment" where
  "open_sibling_produced \<equiv> finite_narrowed_commitment open_sibling_program 0 input_control_declarations lookup_frames"

text \<open>
  At bound 30 the value is the stored artifact; the true call is resolved in 25 states with the production against 53
  without it, one certificate each (26 before the first join below a ground focus, task 821: the produced goal's
  sub-search, ground, keeps its first found state); the false call is refuted in 6 states and the lookup of another artifact in 23. R4
  gives the same three verdicts. With 26's sibling open (@{const open_sibling_program}), the true call is resolved in 30
  states with the production against 58 without it, and the false call refuted in 6; R4 gives the same two verdicts.
\<close>

lemma input_production_controls:
  "witness_value (finite_collection_construction [identity_input_registration] 0) input_control_program 12
      identity_socket_schema {|(0,input_control_artifact)|} 1 = Some input_control_artifact \<and>
    input_control_row input_control_produced 40 (input_control_call [5]) 30 = (Some True,1,25) \<and>
    input_control_row input_control_committed 40 (input_control_call [5]) 30 = (Some True,1,53) \<and>
    input_control_plain 40 (input_control_call [5]) = Some True \<and>
    input_control_row input_control_produced 40 (input_control_call [7]) 30 = (Some False,0,6) \<and>
    input_control_plain 40 (input_control_call [7]) = Some False \<and>
    input_control_row input_control_produced 37 (input_control_lookup [Finite_Payload [3],Finite_Payload [1]]) 30 =
      (Some False,0,23) \<and>
    input_control_plain 37 (input_control_lookup [Finite_Payload [3],Finite_Payload [1]]) = Some False \<and>
    input_control_run open_sibling_program open_sibling_produced 40 (input_control_call [5]) 30 = (Some True,1,30) \<and>
    input_control_run open_sibling_program input_control_committed 40 (input_control_call [5]) 30 = (Some True,1,58) \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction open_sibling_program 40
      (input_control_call [5]) 30) = Some True \<and>
    input_control_run open_sibling_program open_sibling_produced 40 (input_control_call [7]) 30 = (Some False,0,6) \<and>
    input_control_run open_sibling_program input_control_committed 40 (input_control_call [7]) 30 = (Some False,0,6) \<and>
    finite_resolution_verdict (finite_program_resolution no_witness_construction open_sibling_program 40
      (input_control_call [7]) 30) = Some False"
  by eval

end
