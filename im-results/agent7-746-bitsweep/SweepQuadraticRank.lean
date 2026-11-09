import SweepMacroOrbit

namespace CascadeFastReturn
open CascadeBitSweep

/-- Additive upper budget for all first-return reset edges at lower levels. -/
def levelWeight : Nat → Nat
  | 0 => 0
  | k+1 => levelWeight k + k+4

private theorem kplus6_le_eight_pow (k : Nat) : k+6 ≤ 8*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.pow_succ]
    omega

/-- The genuine dyadic-level deficit is strictly less than 16·2^k. -/
theorem level_deficit_lt_pow (h : Nat) :
    deficitAt (firstFailIndex h) h < 2^(firstFailIndex h+4) := by
  let k := firstFailIndex h
  have hp := kplus6_le_eight_pow k
  have hh := (firstFailIndex_spec h).2
  have he : 2^(k+4)=16*2^k := by rw [Nat.pow_add]; simp [Nat.mul_comm]
  change deficitAt k h < 2^(k+4)
  rw [he]
  dsimp [deficitAt]
  omega

/-- The source-level binary deficit log never exceeds its level by three. -/
theorem level_deficit_log_bound (h : Nat) :
    (deficitAt (firstFailIndex h) h).log2 ≤ firstFailIndex h+3 := by
  have hlo := level_deficit_min h
  have hlt := level_deficit_lt_pow h
  have hne : deficitAt (firstFailIndex h) h ≠0 := by omega
  exact Nat.le_of_lt_succ ((Nat.log2_lt hne).2 hlt)

/-- An integer potential for every original-source first-return reset. -/
def visitRank (h : Nat) : Nat :=
  let k := firstFailIndex h
  levelWeight k + (k+4-(deficitAt k h).log2)

/-- Every genuine source height has an integral rank strictly inside its
    level budget, with no synthetic preparation assumptions. -/
theorem visitRank_bounds (h : Nat) :
    levelWeight (firstFailIndex h)+1 ≤ visitRank h ∧
    visitRank h ≤ levelWeight (firstFailIndex h+1) := by
  have hh := level_deficit_log_bound h
  dsimp [visitRank]
  change levelWeight (firstFailIndex h)+1 ≤
    levelWeight (firstFailIndex h)+(firstFailIndex h+4-(deficitAt (firstFailIndex h) h).log2) ∧
    levelWeight (firstFailIndex h)+(firstFailIndex h+4-(deficitAt (firstFailIndex h) h).log2) ≤
    levelWeight (firstFailIndex h+1)
  rw [levelWeight]
  omega

theorem levelWeight_mono (k l : Nat) (hkl : k≤l) : levelWeight k≤levelWeight l := by
  induction l with
  | zero =>
    have hk : k=0 := by omega
    subst k
    exact Nat.le_refl _
  | succ l ih =>
    by_cases h : k≤l
    · have hleft := ih h
      change levelWeight k≤levelWeight l+(l+4)
      omega
    · have heq : k=l+1 := by omega
      subst k
      exact Nat.le_refl _

/-- A successful source reset at the same level raises this rank exactly one. -/
theorem visitRank_same_level_one (h u : Nat)
    (ho : bitOutcome h=some u)
    (hsame : firstFailIndex h=firstFailIndex u) :
    visitRank u=visitRank h+1 := by
  let k := firstFailIndex h
  have hhalf := (same_address_forces_half_deficit h u ho hsame).2
  have hne : deficitAt k u ≠0 := by
    have hu := level_deficit_min u
    rw [←hsame] at hu
    change 2*k+6≤deficitAt k u at hu
    omega
  have hlog : (deficitAt k h).log2=(deficitAt k u).log2+1 := by
    rw [hhalf]
    exact Nat.log2_two_mul hne
  have hb := level_deficit_log_bound h
  have hbu := level_deficit_log_bound u
  rw [←hsame] at hbu
  dsimp [visitRank]
  rw [←hsame]
  change levelWeight k + (k+4-(deficitAt k u).log2) =
      levelWeight k+(k+4-(deficitAt k h).log2)+1
  have hb2 : (deficitAt k h).log2≤k+3 := by simpa [k] using hb
  omega

/-- Every successful original-source first reset strictly raises the same
    global integer potential, including odd multi-level jumps. -/
theorem visitRank_strict (h u : Nat)
    (ho : bitOutcome h=some u) : visitRank h<visitRank u := by
  have hm := bitOutcome_address_monotone h u ho
  by_cases he : firstFailIndex h=firstFailIndex u
  · have hone := visitRank_same_level_one h u ho he
    omega
  · have hlt : firstFailIndex h+1≤firstFailIndex u := by omega
    have hlow := (visitRank_bounds u).1
    have hhigh := (visitRank_bounds h).2
    have hmono := levelWeight_mono (firstFailIndex h+1)
        (firstFailIndex u) hlt
    omega

/-- An n-edge successful original source reset path increases rank by n. -/
theorem runBit_visitRank_lower (start n u : Nat)
    (hu : runBit start n=some u) :
    n+visitRank start≤visitRank u := by
  induction n generalizing u with
  | zero =>
    simp [runBit] at hu
    subst u
    omega
  | succ n ih =>
    cases hp : runBit start n with
    | none =>
      simp [runBit,hp] at hu
    | some h =>
      have he : bitOutcome h=some u := by simpa [runBit,hp] using hu
      have hprev := ih h hp
      have hrank := visitRank_strict h u he
      omega

/-- Universal quadratic halt-or-level-escape bound: a successful n-step
    source return ending in level at most L requires n ≤ Σ_{k=0}^L (k+4).
    This says nothing about whether a true blank-root fatal state occurs. -/
theorem successful_run_quadratic_level_bound (start n u L : Nat)
    (hu : runBit start n=some u)
    (hL : firstFailIndex u≤L) :
    n≤levelWeight (L+1) := by
  have hprogress := runBit_visitRank_lower start n u hu
  have hupper := (visitRank_bounds u).2
  have hmono := levelWeight_mono (firstFailIndex u+1) (L+1) (by omega)
  omega

#print axioms level_deficit_log_bound
#print axioms visitRank_same_level_one
#print axioms visitRank_strict
#print axioms successful_run_quadratic_level_bound
end CascadeFastReturn
