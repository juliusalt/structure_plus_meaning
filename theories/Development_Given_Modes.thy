theory Development_Given_Modes
  imports Factor_Resolution_Modes Factor_Root_Family_Declarations Development_Asked_Registrations
    Development_First_Request_Registrations
begin

text \<open>
  The given's modes (O4 of correction (12) of "Committed choice, for refusals", DECISIONS.md, task 495's entry): the
  data selection 5, its argument (element, (list, rest)), read at two views. At the \<^emph>\<open>row view\<close> ((k,v),(l,r)) its
  input is (k,l) and its output (v,r): a keyed element's key and the list in, its value and the rest out, the lookup
  37's clause makes of the environment's artifact rows (5 at 37.0/1, binding 12's input). At the \<^emph>\<open>whole view\<close>
  (e,(l,r)) its input is (e,l) and its output r: in a bag check the element and the list are ground and the rest is
  returned (5 at 6.0/0, binding 6.1/1's output). A mode carries no obligation and is read by the selection alone
  (@{const finite_moded_priority}); no consumer declaration is added for 5 or 0 (correction (12), "113's 6").

  The sites are the given's numbered readers' (@{const finite_rooted_given_readers}), which the asked program and the
  first request's program keep with their clauses (@{thm [source] asked_additions_readers_agreement},
  @{thm [source] first_request_readers_agreement}): at those three programs the modes are @{text given_modes}
  itself. The whole view is the selection's view the root family's records declare (@{const selection_view}). Where the programs are installed, the modes are relocated by O1's relocation with the placements the
  records' carrying uses (@{const given_readers_placement}, @{const asked_additions_placement},
  @{const first_request_placement}), the views kept.
\<close>

definition given_row_view :: "nat resolution_view" where
  "given_row_view = (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)),
    Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 2),
    Finite_Pattern_Pair (Finite_Variable 1) (Finite_Variable 3))"

definition given_modes :: "nat resolution_modes" where
  "given_modes = {|(5,given_row_view),(5,selection_view)|}"

lemma given_row_view_formed: "view_formed given_row_view"
  by (auto simp: view_formed_def given_row_view_def fset_eq_iff)

lemmas given_views_formed = given_row_view_formed selection_view_formed

lemma given_modes_formed: "modes_formed given_modes"
  using given_views_formed by (simp add: modes_formed_def given_modes_def)

lemma given_modes_member: "(d,V) |\<in>| given_modes \<longleftrightarrow> d = 5 \<and> (V = given_row_view \<or> V = selection_view)"
  by (auto simp: given_modes_def)

lemma given_modes_sites: "fst ` fset given_modes = {5}"
  by (auto simp: given_modes_def)

section \<open>The modes where the programs are installed\<close>

text \<open>
  Relocated by the placement that carries the records (@{text declarations_relocated}), a mode keeps its view and
  moves its site: each installed program's modes are the given's two views at the placed site of 5.
\<close>

lemma given_modes_relocated: "modes_relocated g given_modes = {|(g 5,given_row_view),(g 5,selection_view)|}"
  by (simp add: modes_relocated_def given_modes_def)

lemma given_modes_relocated_formed: "modes_formed (modes_relocated g given_modes)"
  using given_views_formed by (simp add: given_modes_relocated modes_formed_def)

definition given_placed_modes :: "local_address option definition_site resolution_modes" where
  "given_placed_modes = modes_relocated given_readers_placement given_modes"

definition asked_additions_placed_modes :: "local_address option definition_site resolution_modes" where
  "asked_additions_placed_modes = modes_relocated asked_additions_placement given_modes"

definition first_request_placed_modes :: "local_address option definition_site resolution_modes" where
  "first_request_placed_modes = modes_relocated first_request_placement given_modes"

lemma given_placed_modes_formed:
  "modes_formed given_placed_modes" "modes_formed asked_additions_placed_modes" "modes_formed first_request_placed_modes"
  by (simp_all only: given_placed_modes_def asked_additions_placed_modes_def first_request_placed_modes_def
    given_modes_relocated_formed)

lemma given_placed_modes_member:
  "(e,V) |\<in>| given_placed_modes \<longleftrightarrow> e = given_readers_placement 5 \<and> (V = given_row_view \<or> V = selection_view)"
  "(e,V) |\<in>| asked_additions_placed_modes \<longleftrightarrow> e = asked_additions_placement 5 \<and> (V = given_row_view \<or> V = selection_view)"
  "(e,V) |\<in>| first_request_placed_modes \<longleftrightarrow>
    e = first_request_placement 5 \<and> (V = given_row_view \<or> V = selection_view)"
  by (auto simp: given_placed_modes_def asked_additions_placed_modes_def first_request_placed_modes_def given_modes_relocated)

lemma given_modes_first_request_sites: "fst ` fset given_modes \<subseteq> system_definitions first_request_program_system"
  using first_request_sites by (simp add: given_modes_sites)

end
