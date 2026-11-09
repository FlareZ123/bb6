import DoubleOddGapRoot
set_option maxHeartbeats 0

namespace CascadeFastReturn
open CascadeBitSweep CascadeResetInverse CascadeSweep

private theorem double_family_pow27 (n : Nat) :
    2^(12+54*n)%27=19 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have heq : 12+54*(n+1)=(12+54*n)+54 := by omega
    rw [heq,Nat.pow_add,Nat.mul_mod,ih]

private theorem double_family_growth (k : Nat) (hk : 12≤k) :
    2*k+25<2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 12≤k
    · have hp := ih h
      rw [Nat.pow_succ]
      omega
    · have he : k=11 := by omega
      subst k
      decide

private theorem double_family_arithmetic (n : Nat) :
  let k := 12+54*n
  let p := 2^k
  let e := 6*p+k+5
  (12*p+k+4≤2*e) ∧
  (4*e+10<27*p) ∧
  ((2*e+5)%27≠0) ∧
  (2*(2*e-8*p-k)+5<9*p) ∧
  ((2*(2*e-8*p-k)+5)%9≠0) ∧
  (4*p≤e+k+4) ∧
  (e+k+5<8*p) ∧
  (e%3=2) ∧
  ((2*e-8*p-k)%3=2) := by
  let k := 12+54*n
  let p := 2^k
  let e := 6*p+k+5
  have hk : 12≤k := by dsimp [k]; omega
  have hg := double_family_growth k hk
  have hpow : p%27=19 := by
    simpa only [p,k] using double_family_pow27 n
  have hk27 : k%27=12 := by dsimp [k]; omega
  have hpm3 : p%3=1 := by omega
  have hk3 : k%3=0 := by dsimp [k]; omega
  have hemod27 : (2*e+5)%27=24 := by dsimp [e]; omega
  have hh : 2*e-8*p-k=4*p+k+10 := by dsimp [e]; omega
  have hhmod9 : (2*(2*e-8*p-k)+5)%9=3 := by
    rw [hh]
    have hpm9 : p%9=1 := by omega
    have hk9 : k%9=3 := by dsimp [k]; omega
    omega
  have hem3 : e%3=2 := by dsimp [e]; omega
  have hhm3 : (2*e-8*p-k)%3=2 := by rw [hh]; omega
  have h1 : 12*p+k+4≤2*e := by dsimp [e]; omega
  have h2 : 4*e+10<27*p := by dsimp [e]; omega
  have h3 : (2*e+5)%27≠0 := by omega
  have h4 : 2*(2*e-8*p-k)+5<9*p := by rw [hh]; omega
  have h5 : (2*(2*e-8*p-k)+5)%9≠0 := by omega
  have h6 : 4*p≤e+k+4 := by dsimp [e]; omega
  have h7 : e+k+5<8*p := by dsimp [e]; omega
  exact ⟨h1,h2,h3,h4,h5,h6,h7,hem3,hhm3⟩

/-- Infinitely many authentic blank-root-unreachable levels k=12+54n,
    e=6·2^k+k+5, in which BOTH e and its uniquely forced even parent
    h=4·2^k+k+10 have residue two modulo three. The level-k target
    fails the narrow exact 27-adic image condition, while the forced
    parent fails the exact middle-low 9-adic image condition. Neither
    obstruction is visible at the corresponding elementary mod-three
    test. -/
theorem double_gap_infinite_root_exclusion (n : Nat) :
    let k := 12+54*n
    let e := 6*2^k+k+5
    (¬ReachC (2,0) (e,0)) ∧
      (e%3=2) ∧ ((2*e-8*2^k-k)%3=2) := by
  let k := 12+54*n
  let e := 6*2^k+k+5
  obtain ⟨hlow,hnarrow,hdiv27,hmiddle,hdiv9,hidxlow,hidxup,heresh,hresh⟩ :=
    double_family_arithmetic n
  have hi : firstFailIndex e=k :=
    firstFailIndex_unique e k hidxup
      (guards_from_low e k hidxlow)
  exact ⟨narrow_27_middle9_root_exclusion k e
      (by dsimp [k]; omega) hi hlow hnarrow hdiv27 hmiddle hdiv9,
    heresh,hresh⟩

#print axioms double_family_arithmetic
#print axioms double_gap_infinite_root_exclusion
end CascadeFastReturn
