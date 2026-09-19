theory RRA_Inserted_Attachments
  imports RRA_Finite_Syntax_Construction
begin

section \<open>Attaching a structure inserts it into the artifact\<close>

text \<open>
  The library executes a union by inserting every member of its left operand into its right one,
  each insertion testing the members already present. Attaching a record or family structure to an
  artifact united the artifact's carrier and incidence, on the left, with the structure's few
  members: every address and row of the whole artifact was inserted into a list that grows to the
  artifact's size, so each attachment cost the square of the artifact, and wrapping the compiled
  definition of a native question over n candidates grew with the fourth power of n. The union is
  the same set with its operands exchanged; the structure's members are then inserted into the
  artifact, at the cost of the artifact's size for each of them.
\<close>

declare finite_attach_structure_def[code del]

lemma finite_attach_structure_inserting_code [code]:
  "finite_attach_structure R H=\<lparr>finite_structure=\<lparr>
    finite_carrier=finite_carrier H |\<union>| finite_carrier (finite_structure R),
    finite_incidence=finite_incidence H |\<union>| finite_incidence (finite_structure R)\<rparr>,
    finite_data=finite_data R\<rparr>"
  by (simp only: finite_attach_structure_def sup_commute)

end
