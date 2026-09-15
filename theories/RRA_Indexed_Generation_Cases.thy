theory RRA_Indexed_Generation_Cases
  imports RRA_Indexed_Generation_Methods RRA_Finite_Generation_Record_Cases
begin

definition indexed_generation_problem :: "nat\<Rightarrow>generation_record_problem" where
  "indexed_generation_problem w=(if w<16 then generation_record_case w else
    let X=generation_record_case (w-16) in case X of (E,l,p,c,rows) \<Rightarrow>
      case generation_record_base X of None \<Rightarrow> X | Some (F,u,G) \<Rightarrow> (F,l,p,c,[((u,[]),G)]))"

fun generation_changed_payload where
  "generation_changed_payload (Generation l P p c)=Generation l P (Finite_Whole (finite_payload_syntax [88])) c"

fun generation_changed_predecessors where
  "generation_changed_predecessors (Generation l P p c)=Generation l (fimage generation_changed_payload P) p c"

definition indexed_generation_queries where
  "indexed_generation_queries l p c rows=(let G=finite_generation_record_core l p c rows in
    rows @ map (\<lambda>(d,H). (d,generation_changed_predecessors H)) rows @
      [((None,[]),G),((Some [99],[]),G),((Some [99],[99]),G)] @
      map (\<lambda>(d,H). ((fst d,[99]),H)) rows)"

definition indexed_generation_case :: "nat\<Rightarrow>indexed_generation_subject" where
  "indexed_generation_case w=(case indexed_generation_problem w of (E,l,p,c,rows) \<Rightarrow>
    (load_digit_environment E,l,p,c,rows,indexed_generation_queries l p c rows))"

definition indexed_generation_original_subject :: "indexed_generation_subject\<Rightarrow>generation_record_problem option" where
  "indexed_generation_original_subject X=(case X of (input,l,p,c,rows,queries) \<Rightarrow>
    map_option (\<lambda>q. (snd (digit_allocated_view q),l,p,c,rows)) input)"

theorem indexed_generation_case_original:
  "indexed_generation_original_subject (indexed_generation_case w)=
    (let X=indexed_generation_problem w in if finite_environment_formed (fst X) then Some X else None)"
proof -
  obtain E l p c rows where shape: "indexed_generation_problem w=(E,l,p,c,rows)"
    by (cases "indexed_generation_problem w") auto
  have observed: "map_option (\<lambda>q. (snd (digit_allocated_view q),l,p,c,rows)) (load_digit_environment E)=
    (if finite_environment_formed E then Some (E,l,p,c,rows) else None)"
    by (rule load_digit_environment_observation[where observe="\<lambda>F. (F,l,p,c,rows)"])
  show ?thesis by (simp only: indexed_generation_case_def indexed_generation_original_subject_def
    shape case_prod_conv Let_def fst_conv observed)
qed

theorem indexed_generation_previous_case:
  "w<16 \<Longrightarrow> indexed_generation_original_subject (indexed_generation_case w)=
    (if finite_environment_formed (fst (generation_record_case w)) then Some (generation_record_case w) else None)"
  by (simp only: indexed_generation_case_original indexed_generation_problem_def if_True Let_def)

definition indexed_generation_source_scope :: "nat list\<Rightarrow>nat list" where
  "indexed_generation_source_scope ws=ws"

definition indexed_generation_previous_cases :: "nat list\<Rightarrow>(nat\<times>generation_record_problem) list" where
  "indexed_generation_previous_cases ws=map (\<lambda>w. (w,indexed_generation_problem w)) (indexed_generation_source_scope ws)"

definition indexed_generation_source_equal :: "indexed_generation_subject\<Rightarrow>generation_record_problem\<Rightarrow>bool" where
  "indexed_generation_source_equal X previous=(indexed_generation_original_subject X=
    (if finite_environment_formed (fst previous) then Some previous else None))"

definition indexed_generation_indices :: "nat list" where
  "indexed_generation_indices=[0..<32]"

text \<open>
  All sixteen original construction requests are retained with their complete
  environments and predecessor sites. Successful original construction adds
  queries of the actual new record, including false claims with unchanged top
  fields and changed predecessor generations. Malformed loading remains absent;
  the original whole source is retained separately for that distinction.
\<close>

end
