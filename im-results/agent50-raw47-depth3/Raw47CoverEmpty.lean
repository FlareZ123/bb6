import CanonicalFrontier
namespace BB6.Agent50
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47CanonicalFrontier
/-- Exact empty residual roster closes a quotient frontier. -/
theorem closeEmptyQuotient {B : Nat} {p : PartialMachine} {α : Type} {remaining : List (α × PartialMachine)}
    (hzero : remaining.length = 0)
    (local_sound : ∀ m, TNFQuotientCompatible p m →
       WeightedBound B m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound B m := by
  intro m hm
  rcases local_sound m hm with hb | ⟨e,he,_⟩
  · exact hb
  · have hnil : remaining = [] := List.length_eq_zero_iff.mp hzero
    simp [hnil] at he
/-- Actual cover at the same bound, with no additional assumptions. -/
theorem coverEmptyQuotient {B : Nat} {p : PartialMachine} {α : Type} {remaining : List (α × PartialMachine)}
    (hzero : remaining.length = 0)
    (local_sound : ∀ m, TNFQuotientCompatible p m →
       WeightedBound B m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m) :
    Cover (WeightedBound B) p :=
  .leaf p (fun m hm => closeEmptyQuotient hzero local_sound m (compatible_quotient hm))
/-- Raise a checked weighted cover to any larger threshold. -/
theorem raiseWeightedCover {B C : Nat} {p : PartialMachine}
    (hBC : B ≤ C) (cert : Cover (WeightedBound B) p) : Cover (WeightedBound C) p :=
  .leaf p (fun m hm n d hn hd => Nat.le_trans (cert.sound m hm n d hn hd) hBC)
#print axioms closeEmptyQuotient
#print axioms coverEmptyQuotient
#print axioms raiseWeightedCover
end BB6.Agent50
