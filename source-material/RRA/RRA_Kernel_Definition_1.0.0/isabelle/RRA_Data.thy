theory RRA_Data
  imports RRA_Core
begin

type_synonym octets = "nat list"

definition octets_formed :: "octets ⇒ bool" where
  "octets_formed xs ⟷ (∀x∈set xs. x < 256)"

datatype data_kind = No_Kind | Bag_Kind | Functional_Kind | Node_Kind

datatype 'a rra_data =
    No_Data
  | Bag_Data "((('a × octets) × nat) set)"
  | Functional_Data "(('a × octets) set)"
  | Node_Data "((('a × 'a) × octets) set)"

fun kind_of :: "'a rra_data ⇒ data_kind" where
  "kind_of No_Data = No_Kind"
| "kind_of (Bag_Data B) = Bag_Kind"
| "kind_of (Functional_Data F) = Functional_Kind"
| "kind_of (Node_Data N) = Node_Kind"

definition bag_formed :: "'a set ⇒ ((('a × octets) × nat) set) ⇒ bool" where
  "bag_formed U B ⟷ finite B ∧
     (∀u v n. ((u,v),n)∈B ⟶ u∈U ∧ octets_formed v ∧ n>0) ∧
     (∀u v n m. ((u,v),n)∈B ∧ ((u,v),m)∈B ⟶ n=m)"

definition functional_formed :: "'a set ⇒ ('a × octets) set ⇒ bool" where
  "functional_formed U F ⟷ finite F ∧
     (∀u v. (u,v)∈F ⟶ u∈U ∧ octets_formed v) ∧
     (∀u v w. (u,v)∈F ∧ (u,w)∈F ⟶ v=w)"

definition node_formed :: "'a set ⇒ (('a × 'a) × octets) set ⇒ bool" where
  "node_formed U N ⟷ finite N ∧
     (∀d u v. ((d,u),v)∈N ⟶ d∈U ∧ u∈U ∧ octets_formed v) ∧
     (∀d u v u' v'. ((d,u),v)∈N ∧ ((d,u'),v')∈N ⟶ u=u' ∧ v=v')"

fun data_formed :: "'a set ⇒ 'a rra_data ⇒ bool" where
  "data_formed U No_Data = True"
| "data_formed U (Bag_Data B) = bag_formed U B"
| "data_formed U (Functional_Data F) = functional_formed U F"
| "data_formed U (Node_Data N) = node_formed U N"

record 'a rra_object =
  base :: "'a rra_structure"
  payload :: "'a rra_data"

definition object_formed :: "'a rra_object ⇒ bool" where
  "object_formed O ⟷ structure_formed (base O) ∧ data_formed (carrier (base O)) (payload O)"

fun rename_data :: "('a ⇒ 'b) ⇒ 'a rra_data ⇒ 'b rra_data" where
  "rename_data f No_Data = No_Data"
| "rename_data f (Bag_Data B) = Bag_Data {((f u,v),n) |u v n. ((u,v),n)∈B}"
| "rename_data f (Functional_Data F) = Functional_Data {(f u,v) |u v. (u,v)∈F}"
| "rename_data f (Node_Data N) = Node_Data {((f d,f u),v) |d u v. ((d,u),v)∈N}"

definition rename_object :: "('a ⇒ 'b) ⇒ 'a rra_object ⇒ 'b rra_object" where
  "rename_object f O = ⦇base=rename_structure f (base O), payload=rename_data f (payload O)⦈"

definition object_iso :: "'a rra_object ⇒ 'b rra_object ⇒ ('a ⇒ 'b) ⇒ bool" where
  "object_iso O P f ⟷ structure_iso (base O) (base P) f ∧ rename_data f (payload O)=payload P"

end
