import SweepAddress

namespace CascadeFastReturn
open CascadeBitSweep

/-- Fatal heights are the exact lower endpoint of their dyadic sweep level. -/
def fatalAt (h : Nat) : Prop :=
  h + firstFailIndex h + 4 = 4*2^(firstFailIndex h)

/-- A successful same-level first reset cannot land at the fatal endpoint. -/
theorem same_level_edge_not_fatal (h u : Nat)
    (ho : bitOutcome h=some u)
    (hsame : firstFailIndex h=firstFailIndex u) :
    ¬fatalAt u := by
  have hlower := firstFailIndex_low h
  have hstep := bitOutcome_strict_direct h u ho
  intro hf
  dsimp [fatalAt] at hf
  rw [←hsame] at hf
  omega

/-- Every directly reached fatal reset must be the first visited height
    in a new dyadic level, rather than part of an even same-level cascade. -/
theorem fatal_target_requires_level_advance (h u : Nat)
    (ho : bitOutcome h=some u) (hf : fatalAt u) :
    firstFailIndex h < firstFailIndex u := by
  have hm := bitOutcome_address_monotone h u ho
  by_cases he : firstFailIndex h=firstFailIndex u
  · exact False.elim (same_level_edge_not_fatal h u ho he hf)
  · omega

#print axioms same_level_edge_not_fatal
#print axioms fatal_target_requires_level_advance
end CascadeFastReturn
