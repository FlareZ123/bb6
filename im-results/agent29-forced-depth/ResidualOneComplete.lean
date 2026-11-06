import ResidualModFive
import SecondOneInfinite
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Barrier

theorem second_one_index_closed (r:Nat) :
  5*(BB6.Agent29Depth.secondOneJ r)+14=2^(4*r+6) := by
  induction r with
  | zero => decide
  | succ r ih =>
      have he : 4*(r+1)+6=(4*r+6)+4 := by omega
      rw [he,Nat.pow_add]
      change 5*(16*BB6.Agent29Depth.secondOneJ r+42)+14 =
        2^(4*r+6)*2^4
      have hf:(2:Nat)^4=16 := by decide
      rw [hf]
      omega

/-- All nonnegative solutions of the m=1 4-residual dyadic equation
    occur in the prior explicit j=10 recurrence family. -/
theorem mone_dyadic_index_complete (j d:Nat)
    (hpow:2^(d+1)=5*j+14) :
    ∃ r, j=BB6.Agent29Depth.secondOneJ r ∧ d=4*r+5 := by
  have hh:(2^(d+1))%5=4 := by omega
  have hmod := mod_five_four (d+1) hh
  have hneq:d≠1 := by
    intro he
    subst d
    simp at hpow
  have hd:5≤d := by omega
  let r := (d-5)/4
  have hdr : d=4*r+5 := by dsimp [r]; omega
  have hpowr : 2^(4*r+6)=5*j+14 := by
    have he:d+1=4*r+6 := by omega
    rw [←he]
    exact hpow
  have hfamily := second_one_index_closed r
  refine ⟨r,?_,hdr⟩
  omega

#print axioms second_one_index_closed
#print axioms mone_dyadic_index_complete
end BB6.Agent29Barrier
