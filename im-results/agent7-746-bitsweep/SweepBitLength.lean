import Std

/-! A two-candidate exact location of the first failed dyadic sweep guard. -/
namespace CascadeBitSweep

private theorem eight_pow (j : Nat) : 8 * 2 ^ j = 2 ^ (j + 3) := by
  rw [Nat.pow_add]
  simp
  omega

private theorem linear_lt_pow (k : Nat) : k + 1 < 2 ^ (k + 3) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have he : 2 ^ (k + 1 + 3) = 2 * 2 ^ (k + 3) := by
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, Nat.pow_succ]
      omega
    rw [he]
    omega

private theorem logarithmic_bracket (h : Nat) :
    let k := (h + 5).log2 - 2
    2 ^ (k + 2) ≤ h + 5 ∧ h + 5 < 2 ^ (k + 3) := by
  dsimp
  have h2 : 2 ≤ (h + 5).log2 := by
    apply (Nat.le_log2 (by omega)).2
    simp
  have heq : (h + 5).log2 - 2 + 2 = (h + 5).log2 := by omega
  constructor
  · rw [heq]
    exact Nat.log2_self_le (by omega)
  · rw [show (h + 5).log2 - 2 + 3 = (h + 5).log2 + 1 by omega]
    exact Nat.lt_log2_self

/-- Candidate at the log2 boundary, with only one possible extra sweep. -/
def firstFailIndex (h : Nat) : Nat :=
  let k := (h + 5).log2 - 2
  if h + k + 5 < 8 * 2 ^ k then k else k + 1

/-- All earlier guards are true, and the returned guard is the first false one. -/
theorem firstFailIndex_spec (h : Nat) :
    (∀ j, j < firstFailIndex h → 8 * 2 ^ j ≤ h + j + 5) ∧
    h + firstFailIndex h + 5 < 8 * 2 ^ firstFailIndex h := by
  let k := (h + 5).log2 - 2
  have hb := logarithmic_bracket h
  change 2 ^ (k + 2) ≤ h + 5 ∧ h + 5 < 2 ^ (k + 3) at hb
  obtain ⟨hl,hu⟩ := hb
  have hbefore (j : Nat) (hj : j < k) : 8 * 2 ^ j ≤ h + j + 5 := by
    rw [eight_pow]
    calc
      2 ^ (j + 3) ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ h + 5 := hl
      _ ≤ h + j + 5 := by omega
  have hnext : h + (k + 1) + 5 < 8 * 2 ^ (k + 1) := by
    have hg := linear_lt_pow k
    have hp : 2 ^ (k + 4) = 2 * 2 ^ (k + 3) := by
      rw [show k + 4 = (k + 3) + 1 by omega, Nat.pow_succ]
      omega
    rw [eight_pow, show k + 1 + 3 = k + 4 by omega, hp]
    omega
  unfold firstFailIndex
  change (∀ j, j < (if h + k + 5 < 8 * 2 ^ k then k else k + 1) →
      8 * 2 ^ j ≤ h + j + 5) ∧
      h + (if h + k + 5 < 8 * 2 ^ k then k else k + 1) + 5 <
      8 * 2 ^ (if h + k + 5 < 8 * 2 ^ k then k else k + 1)
  by_cases hf : h + k + 5 < 8 * 2 ^ k
  · simp only [if_pos hf]
    exact ⟨fun j hj => hbefore j hj, hf⟩
  · simp only [if_neg hf]
    constructor
    · intro j hj
      by_cases hjk : j < k
      · exact hbefore j hjk
      · have he : j = k := by omega
        subst j
        omega
    · exact hnext

/-- The least failing index is uniquely determined by its two guard conditions. -/
theorem firstFailIndex_unique (h k : Nat)
    (hfirst : h + k + 5 < 8 * 2 ^ k)
    (hearlier : ∀j, j < k → 8 * 2 ^ j ≤ h + j + 5) :
    firstFailIndex h = k := by
  obtain ⟨hp, hf⟩ := firstFailIndex_spec h
  rcases Nat.lt_trichotomy (firstFailIndex h) k with hlt | heq | hgt
  · have := hearlier _ hlt
    omega
  · exact heq
  · have := hp _ hgt
    omega

/-- The least failing sweep level is monotone in the reset height. -/
theorem firstFailIndex_mono (h u : Nat) (hu : h≤u) :
    firstFailIndex h ≤ firstFailIndex u := by
  obtain ⟨hp, _⟩ := firstFailIndex_spec h
  have hf := (firstFailIndex_spec u).2
  by_cases hh : firstFailIndex h ≤ firstFailIndex u
  · exact hh
  have hlt : firstFailIndex u < firstFailIndex h := by omega
  have hguard := hp (firstFailIndex u) hlt
  omega

/-- Crossing 8·2^k forces the next failed sweep level past k. -/
theorem firstFailIndex_gt_of_eight (k u : Nat) (hu : 8*2^k ≤ u) :
    k < firstFailIndex u := by
  have hf := (firstFailIndex_spec u).2
  by_cases hh : k < firstFailIndex u
  · exact hh
  have hle : firstFailIndex u ≤ k := by omega
  have hp : 2^(firstFailIndex u) ≤ 2^k :=
    Nat.pow_le_pow_right (by omega) hle
  have hscale := Nat.mul_le_mul_left 8 hp
  omega

#print axioms firstFailIndex_mono
#print axioms firstFailIndex_gt_of_eight

#print axioms firstFailIndex_spec
#print axioms firstFailIndex_unique

end CascadeBitSweep
