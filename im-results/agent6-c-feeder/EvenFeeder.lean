import Agent3COrbitIff
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent6

open BB6.Agent3

/-- Every positive even member of the exact affine (1,4j) feeder family
    violates the true blank-section modulo-four invariant. -/
theorem no_even_feeder (t : Nat) (ht : 1 ≤ t) :
    ¬ CReach (8*t-1) (4*t-1) := by
  rintro ⟨time, h⟩
  have hy : (4*t-1)%2=1 := by omega
  have hs : ((8*t-1)+(4*t-1))%4=2 := by omega
  have hb := BB6Agent38.blank_section_mod4 time
    (8*t-1) (4*t-1) h hy hs
  have ha := (Prod.mk.inj hb).1
  omega

/-- Authentic Machine C zero-counter sections never reach (1,8t) for t≥1.
    This combines Agent3's exact predecessor equivalence with Agent38's
    all-time blank-orbit output invariant. -/
theorem blank_no_one_eight (t : Nat) (ht : 1 ≤ t) :
    ¬ CReach 1 (8*t) := by
  intro h
  have h4 : 4*(2*t)=8*t := by omega
  have ha : 4*(2*t)-1=8*t-1 := by omega
  have hk : 2*(2*t)-1=4*t-1 := by omega
  have H : CReach 1 (4*(2*t)) := by simpa only [h4] using h
  have F := (blank_one_four_iff_feeder (2*t) (by omega)).mp H
  rw [ha,hk] at F
  exact no_even_feeder t ht F

#print axioms no_even_feeder
#print axioms blank_no_one_eight

end BB6.Agent6
