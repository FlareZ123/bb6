import MiddleLowOddGap
set_option maxHeartbeats 0

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeSweep

private theorem middle_family_pow9 (n : Nat) :
    2^(10+6*n)%9=7 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have heq : 10+6*(n+1)=(10+6*n)+6 := by omega
    rw [heq,Nat.pow_add,Nat.mul_mod,ih]

/-- Explicit all-index no-parent reset heights in the dyadic middle gap.
    Each height has residue 2 mod3, so it survives a mere mod3 sieve. -/
theorem middle_low_infinite_root_exclusion (n : Nat) :
    let k := 10+6*n
    ¬ ReachC (2,0) (4*2^k+4,0) ∧ (4*2^k+4)%3=2 := by
  let k := 10+6*n
  let p := 2^k
  let h := 4*p+4
  have hp9 : p%9=7 := middle_family_pow9 n
  have hp3 : p%3=1 := by omega
  have hp13 : 13<p := by
    have hp := Nat.pow_le_pow_right
      (by decide : 0<2) (show 10≤k by dsimp [k]; omega)
    have hbase : (13:Nat)<2^10 := by decide
    omega
  have hdiv : (2*h+5)%9=6 := by dsimp [h]; omega
  have hres : h%3=2 := by dsimp [h]; omega
  have htop : 2*h+5<9*2^k := by dsimp [h,p]; omega
  have hlow : 4*2^k≤h := by dsimp [h,p]; omega
  have hne : ¬ReachC (2,0) (h,0) :=
    middle_low_root_nonimage k h
      (by dsimp [k]; omega) hlow htop (by omega)
  exact ⟨hne,hres⟩

#print axioms middle_low_infinite_root_exclusion
end CascadeFastReturn
