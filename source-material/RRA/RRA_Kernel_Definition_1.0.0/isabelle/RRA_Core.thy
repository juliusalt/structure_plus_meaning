theory RRA_Core
  imports Main
begin

record 'a rra_structure =
  carrier :: "'a set"
  incidence :: "('a × 'a × 'a) set"

definition structure_formed :: "'a rra_structure ⇒ bool" where
  "structure_formed S ⟷
     finite (carrier S) ∧ finite (incidence S) ∧
     (∀r p x. (r,p,x) ∈ incidence S ⟶
        r ∈ carrier S ∧ p ∈ carrier S ∧ x ∈ carrier S)"

definition rename_structure :: "('a ⇒ 'b) ⇒ 'a rra_structure ⇒ 'b rra_structure" where
  "rename_structure f S =
     ⦇ carrier = f ` carrier S,
       incidence = (λ(r,p,x). (f r,f p,f x)) ` incidence S ⦈"

definition structure_iso ::
  "'a rra_structure ⇒ 'b rra_structure ⇒ ('a ⇒ 'b) ⇒ bool" where
  "structure_iso S T f ⟷
     bij_betw f (carrier S) (carrier T) ∧ rename_structure f S = T"

definition bounded_iso ::
  "'a rra_structure ⇒ 'b rra_structure ⇒ ('a ⇒ 'b) ⇒
   ('k ⇒ 'a option) ⇒ ('k ⇒ 'b option) ⇒ bool" where
  "bounded_iso S T f b c ⟷
     structure_iso S T f ∧ (∀k. map_option f (b k) = c k)"

end
