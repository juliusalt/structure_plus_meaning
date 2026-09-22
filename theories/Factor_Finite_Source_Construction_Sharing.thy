theory Factor_Finite_Source_Construction_Sharing
  imports Factor_Finite_Source_Construction
begin

section \<open>A source constructor reads its source once\<close>

text \<open>
  A source constructor reads its native source to find the program it extends, and the installation it
  then makes reads the same source again to establish the extension's context. Both readings are of one
  environment at one site, so they are one reading: the equation below reads the source once and passes
  the program it returns to the context's two remaining checks and to the installation. This is the
  invariant computed once of the entry "The in-place refinements apply two notions: a check made where
  its premise is established, and a generator of the accepted candidates": it applies HOL's case
  analysis to the one reading, here the one case scrutinee, and there is no notion to instantiate. The
  constructor, its result and its contract are unchanged on every input.
\<close>

declare finite_construct_source_def[code del]

lemma finite_construct_source_read_once [code]:
  "finite_construct_source supported C E pu pr=(case finite_native_source E pu pr of None \<Rightarrow> None
    | Some P \<Rightarrow> if \<not>supported P then None else (case C P of None \<Rightarrow> None
      | Some (e,Q) \<Rightarrow> if e |\<in>| finite_system_definitions Q \<and> finite_system_formed Q \<and>
          finite_system_agrees_on P Q (finite_system_definitions P)
        then map_option (\<lambda>(F,u). (finite_program_coordinates E (finite_system_definitions P)
          (finite_system_definitions Q) id e,F,u)) (finite_extend_mapped_native E P Q id)
        else None))"
  by (cases "finite_native_source E pu pr"; cases "C (the (finite_native_source E pu pr))";
      cases "finite_extend_mapped_native E (the (finite_native_source E pu pr))
        (snd (the (C (the (finite_native_source E pu pr))))) id")
    (auto simp: finite_construct_source_def finite_native_source_target_def finite_install_source_entry_def
      finite_extend_source_native_def finite_source_extension_context_def split: prod.splits)

end
