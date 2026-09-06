theory RRA_Artifact
  imports RRA_Data
begin

type_synonym address = octets
type_synonym exact_record = "address rra_object"

definition record_formed :: "exact_record ⇒ bool" where
  "record_formed R ⟷ object_formed R ∧ (∀a∈carrier (base R). octets_formed a)"

definition exact_artifact_equal :: "exact_record ⇒ exact_record ⇒ bool" where
  "exact_artifact_equal R S ⟷ R=S"

datatype record_ref = Record_Ref string string octets

datatype citation = Citation record_ref address

definition citation_formed ::
  "(record_ref ⇒ exact_record option) ⇒ citation ⇒ bool" where
  "citation_formed resolve c ⟷
     (case c of Citation ref a ⇒
        (∃R. resolve ref=Some R ∧ record_formed R ∧ a∈carrier (base R)))"

definition record_iso :: "exact_record ⇒ exact_record ⇒ (address ⇒ address) ⇒ bool" where
  "record_iso R S f ⟷ object_iso R S f"

end
