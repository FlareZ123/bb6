import UpperHighRootGap
set_option maxHeartbeats 0

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeSweep

private theorem upper_family_pow_mod3 (n : Nat) :
    2^(8+6*n)%3=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have heq : 8+6*(n+1)=(8+6*n)+6 := by omega
    rw [heq, Nat.pow_add, Nat.mul_mod, ih]

private theorem upper_family_growth (n : Nat) :
    10+6*n+10<5*2^(8+6*n) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have heq : 8+6*(n+1)=(8+6*n)+6 := by omega
    rw [heq, Nat.pow_add]
    have hp : 1≤2^(8+6*n) := Nat.one_le_pow _ _ (by decide)
    change 10+6*(n+1)+10 < 5*(2^(8+6*n)*64)
    omega

private theorem upper_family_arithmetic (n : Nat) :
  let k := 10+6*n
  let e := 27*2^(8+6*n)+5
  (12*2^k+k+4≤2*e) ∧
  (2*e+2≤14*2^k+k) ∧
  (27*2^k≤4*e+10) ∧
  ((2*e+5)%9≠0) ∧
  ((2*e-8*2^k-k)%3≠2) ∧
  (4*2^k≤e+k+4) ∧
  (e+k+5<8*2^k) := by
  let k := 10+6*n
  let p := 2^(8+6*n)
  let e := 27*p+5
  have hk : k=8+6*n+2 := by dsimp [k]; omega
  have heq : 2^k=4*p := by
    rw [hk, Nat.pow_add]
    simp [p]
    omega
  have hmod : p%3=1 := upper_family_pow_mod3 n
  have hkmod : k%3=1 := by dsimp [k]; omega
  have hg : k+10<5*p := upper_family_growth n
  have hp : 1≤p := Nat.one_le_pow _ _ (by decide)
  have hemod : (2*e+5)%9=6 := by
    dsimp [e]
    omega
  have hpm : (2*e-8*2^k-k)%3=1 := by
    rw [heq]
    dsimp [e]
    omega
  dsimp only [k, e]
  have hp2 : 2^(10+6*n)=4*2^(8+6*n) := by simpa only [k,p] using heq
  rw [hp2]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

/-- A new infinite family of genuine blank-root-unreachable first-reset
    heights in the UPPER odd-image band. Every target is 2 modulo 3,
    so the elementary odd-image mod-three obstruction is insufficient.
    The first target is 6917; all n are excluded at every finite time. -/
theorem upper_high_infinite_root_exclusion (n : Nat) :
    let k := 10+6*n
    ¬ ReachC (2,0) (27*2^(8+6*n)+5,0) := by
  let k := 10+6*n
  let e := 27*2^(8+6*n)+5
  have hk : 3≤k := by dsimp [k]; omega
  obtain ⟨hlo,hceiling,hupper,hdiv,hmod,hlow,hguard⟩ :=
    upper_family_arithmetic n
  have hindex : firstFailIndex e=k :=
    firstFailIndex_unique e k hguard
      (guards_from_low e k hlow)
  exact upper_high_root_gap_exclusion k e hk hindex hlo hceiling
    hupper hdiv hmod

#print axioms upper_family_arithmetic
#print axioms upper_high_infinite_root_exclusion
end CascadeFastReturn
