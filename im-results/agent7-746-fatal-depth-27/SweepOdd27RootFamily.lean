import SweepOdd27RootGap
set_option maxHeartbeats 0

namespace CascadeFastReturn
open CascadeBitSweep CascadeSweep

private theorem family_pow27 (n : Nat) :
    2^(9+54*n)%27=26 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have ht : 9+54*(n+1)=(9+54*n)+54 := by omega
    rw [ht, Nat.pow_add, Nat.mul_mod, ih]

private theorem family_exponent_dominates (k : Nat) (hk : 9≤k) :
    4*k+18<3*2^k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : 9≤k
    · have hp := ih h
      rw [Nat.pow_succ]
      omega
    · have he : k=8 := by omega
      subst k
      decide

private theorem family_arithmetic (n : Nat) :
 let k := 9+54*n
 let e := 6*2^k+k+2
 (12*2^k+k+4≤2*e) ∧ (4*e+10<27*2^k) ∧
 ((2*e+5)%27≠0) ∧ ((2*e-8*2^k-k)%3≠2) := by
  let k := 9+54*n
  let e := 6*2^k+k+2
  have hk : 9≤k := by dsimp [k]; omega
  have hp := family_pow27 n
  have hpow : (2^k)%27=26 := by simpa only [k] using hp
  have hpmod3 : (2^k)%3=2 := by omega
  have hkmod3 : k%3=0 := by dsimp [k]; omega
  have hnum : (2*e+5)%27=15 := by
    dsimp [e]
    omega
  have hmod : (2*e-8*2^k-k)%3=0 := by
    dsimp [e]
    omega
  have hg := family_exponent_dominates k hk
  constructor
  · change 12*2^k+k+4≤2*e
    omega
  constructor
  · change 4*e+10<27*2^k
    omega
  constructor
  · omega
  · omega

/-- Uniform infinitely extensible genuine blank-root exclusion, with each
    source reset target e_n in the narrow high odd-image interval and in
    residue 2 mod3. k_n=9+54n grows unboundedly; e_n=6·2^k_n+k_n+2.
    The first parent is forced even by a 27-adic source theorem, and this
    unique predecessor has no parents by the next dyadic gap and mod3. -/
theorem narrow_high_infinite_root_exclusion (n : Nat) :
    let k := 9+54*n
    ¬ ReachC (2,0) (6*2^k+k+2,0) := by
  let k := 9+54*n
  let e := 6*2^k+k+2
  have hk : 9≤k := by dsimp [k]; omega
  have hdom := family_exponent_dominates k hk
  have hlow : 4*2^k≤e+k+4 := by dsimp [e]; omega
  have hupper : e+k+5<8*2^k := by
    dsimp [e]
    omega
  have hindex : firstFailIndex e=k :=
    firstFailIndex_unique e k hupper
      (CascadeResetInverse.guards_from_low e k hlow)
  have ha : (12*2^k+k+4≤2*e) ∧
      (4*e+10<27*2^k) ∧
      ((2*e+5)%27≠0) ∧
      ((2*e-8*2^k-k)%3≠2) := by
    simpa only [k,e] using family_arithmetic n
  exact narrow_high_root_gap_exclusion k e (by omega) hindex
    ha.1 ha.2.1 ha.2.2.1 ha.2.2.2

#print axioms narrow_high_infinite_root_exclusion
end CascadeFastReturn
