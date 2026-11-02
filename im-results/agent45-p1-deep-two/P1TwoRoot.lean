import GInverse

namespace BB6.Agent45TwoRoot
open BB6.P1Reduction

/-- Complete G inverse preimage trichotomy for the full positive-odd
    critical-root shape in the surviving 2 (mod 16) sector. -/
theorem root_inverse_three (u k c : Nat)
    (hu : u % 2 = 1) (h : GAncestor (8*u+4) 3 k c) :
    (k=2*u ∧ c=4*u+5) ∨
    (k=3*u+1 ∧ c=2*u+1) ∨
    (2*k=7*u+3 ∧ c=u-1) := by
  generalize hb : 8*u+4 = b at h
  generalize hd : (3:Nat) = d at h
  induction h generalizing u with
  | upper k d =>
      left
      constructor <;> omega
  | nest b d k c h ih =>
      subst d
      rcases (ih u hu hb rfl) with ⟨hk,hc⟩ | ⟨hk,hc⟩ | ⟨hk,hc⟩
      · right; left
        constructor <;> omega
      · right; right
        constructor <;> omega
      · omega

#print axioms root_inverse_three
end BB6.Agent45TwoRoot
