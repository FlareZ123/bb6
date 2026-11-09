import CSixSeventhGateWide
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 500000

namespace BB6.Agent4Seven
open BB6.Agent46

private theorem parity_sum (j m : Nat)
    (h : (3*m)%4096=(j+2879)%4096) :
    (j+3*m)%4096=(2*j+2879)%4096 := by omega

private theorem parts_split (j : Nat) (hj : j%512=319) :
    j%2048=319 ∨ j%2048=831 ∨ j%2048=1343 ∨ j%2048=1855 := by omega

/-- Exact equivalence between the original four high stopping classes and
    a single coherent two-condition affine congruence ray. -/
theorem fourclass_iff_diagonal (j m : Nat) :
    ((j%2048=319 ∧ (j+3*m)%4096=3517) ∨
      (j%2048=831 ∧ (j+3*m)%4096=445) ∨
      (j%2048=1343 ∧ (j+3*m)%4096=1469) ∨
      (j%2048=1855 ∧ (j+3*m)%4096=2493)) ↔
      (j%512=319 ∧ (3*m)%4096=(j+2879)%4096) := by
  constructor
  · intro h
    rcases h with h | h | h | h
    all_goals omega
  · rintro ⟨hj,hm⟩
    have hs := parity_sum j m hm
    rcases parts_split j hj with h | h | h | h
    · left; omega
    · right; left; omega
    · right; right; left; omega
    · right; right; right; omega

/-- Every original high-stopping candidate on this single affine diagonal
    is absent from the authentic blank section at all times, no cutoff. -/
theorem high_stop_six_seven_diagonal (j m k time : Nat)
    (hm : 7≤m)
    (hj : j%512=319)
    (hpair : (3*m)%4096=(j+2879)%4096)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j+3,k) := by
  have hc := (fourclass_iff_diagonal j m).mpr ⟨hj,hpair⟩
  exact high_stop_six_seven_fourclass_exclusion j m k time hm hc hstop

#print axioms fourclass_iff_diagonal
#print axioms high_stop_six_seven_diagonal
end BB6.Agent4Seven
