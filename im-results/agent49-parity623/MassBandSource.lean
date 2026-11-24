import Agent49InverseWindowSource
import Agent49MassBandArithmetic

/-! Two-scale growth of the exact section map, including zero-budget drains. -/
namespace BB6.Agent49MassBandSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49FlatDrainSource BB6.Agent49InverseWindowSource

/-- Coarse first-coordinate drift and both third-coordinate and joint mass
bounds. No positivity assumption on the input or intermediate budget. -/
def DrainMass (A b z x y : Nat) : Prop :=
  A ≤ x+b ∧ z+3*b ≤ y ∧ A+z+3*b ≤ x+y

theorem drain_mass (A b z x y : Nat)
    (h : drainB A b z = some (.D x y)) : DrainMass A b z x y := by
  unfold DrainMass
  induction b using Nat.strongRecOn generalizing A z with
  | ind b ih =>
    by_cases hb : b=0
    · subst b
      rw [drainB] at h
      simp at h
      obtain ⟨h1,h2⟩ := h
      omega
    · let q := b/3
      have hrep : b=3*q+b%3 := by dsimp [q]; omega
      by_cases hr0 : b%3=0
      · have hq : 0<q := by omega
        have he : b=3*q := by omega
        rw [he,drain_three A q z hq] at h
        have hh := ih (q-1) (by omega) (A+1) (z+6*q+3) h
        omega
      · by_cases hr1 : b%3=1
        · have he : b=3*q+1 := by omega
          by_cases ha : A=0
          · subst A; rw [he,drain_three_one_zero] at h; contradiction
          · rw [he,drain_three_one A q z (by omega)] at h
            have hh := ih q (by omega) (A-1) (z+6*q+7) h
            omega
        · have he : b=3*q+2 := by omega
          by_cases ha : A=0
          · subst A; rw [he,drain_three_two_zero] at h
            have hh := ih q (by omega) 0 (z+6*q+7) h
            omega
          · rw [he,drain_three_two A q z (by omega)] at h
            have hh := ih (q+1) (by omega) (A-1) (z+6*q+5) h
            omega

/-- Every successful transition increases the total mass by at least the
smaller input plus four. If the input is sufficiently unbalanced, its
smaller counter grows at least as fast as m ↦ 2m+1. -/
theorem next_two_scale (a d x y : Nat)
    (h : highLevelNext (.D a d) = some (.D x y)) :
    a+d+min a d+4 ≤ x+y ∧
    (5*min a d+9 ≤ a+d → 2*min a d+1 ≤ min x y) := by
  have hp := parent_envelope_complete DrainMass drain_mass a d x y h
  unfold ParentEnvelope at hp
  rcases hp with hax | hlo | hle | hdiag | hro | hre
  · rcases hax with ⟨ha, he | ho⟩
    · simp_all [Nat.min_def]; split <;> omega
    · simp_all [Nat.min_def]; split <;> omega
  · rcases hlo with ⟨A,b,hd,had,hA,hb,hw⟩
    unfold DrainMass at hw
    rw [Nat.min_eq_right (by omega : d ≤ a)]
    constructor
    · omega
    · intro hm; apply Nat.le_min.mpr; omega
  · rcases hle with ⟨A,b,hd,had,hA,hb,hw⟩
    unfold DrainMass at hw
    rw [Nat.min_eq_right (by omega : d ≤ a)]
    constructor
    · omega
    · intro hm; apply Nat.le_min.mpr; omega
  · rcases hdiag with ⟨ha,he,hw⟩
    unfold DrainMass at hw
    rw [Nat.min_eq_right (by omega : d ≤ a)]
    constructor
    · omega
    · omega
  · rcases hro with ⟨A,b,ha,hd,hA,hD,hw⟩
    unfold DrainMass at hw
    by_cases hh : a≤d
    · rw [Nat.min_eq_left hh]
      constructor
      · omega
      · intro hm; apply Nat.le_min.mpr; omega
    · rw [Nat.min_eq_right (by omega : d≤a)]
      constructor
      · omega
      · omega
  · rcases hre with ⟨A,b,ha,hd,hA,hD,hw⟩
    unfold DrainMass at hw
    by_cases hh : a≤d
    · rw [Nat.min_eq_left hh]
      constructor
      · omega
      · intro hm; apply Nat.le_min.mpr; omega
    · rw [Nat.min_eq_right (by omega : d≤a)]
      constructor
      · omega
      · omega

/-- Exact successful chains in the imported original high-level map. -/
inductive Chain : Nat → Nat → Nat → Nat → Nat → Prop where
  | zero (a d : Nat) : Chain 0 a d a d
  | step {k a d b c x y : Nat} : Chain k a d b c →
      highLevelNext (.D b c) = some (.D x y) → Chain (k+1) a d x y

open BB6.Agent49MassBandArithmetic

theorem chain_path {k a d x y : Nat} (h : Chain k a d x y) :
    Path k (a+d) (min a d) (x+y) (min x y) := by
  induction h with
  | zero a d =>
    apply Path.zero
    have h := Nat.min_le_left a d
    omega
  | @step k a d b c x y h ht ih =>
    have hb := next_two_scale b c x y ht
    have hm := Nat.min_le_left x y
    apply Path.step ih (by omega) (by omega)
    by_cases hs : 5*min b c+9 ≤ b+c
    · right
      have h := hb.2 hs
      omega
    · left; omega

/-- A source-derived polylogarithmic upper bound on the length of any
successful chain ending in a given binary mass band. -/
theorem chain_length {k a d x y : Nat} (h : Chain k a d x y)
    (hs : 0<a+d) (N : Nat) (hx : x+y<2^N) : k≤4*N*N+5*N :=
  path_length (chain_path h) hs N hx

/-- Iteration from the authentic section D(0,7). This is definitionally
identical to the earlier blank-root iteration. -/
def rootRun : Nat → Option HighLevelState
  | 0 => some (.D 0 7)
  | k+1 => (rootRun k).bind highLevelNext

theorem rootRun_chain (k x y : Nat) (h : rootRun k=some (.D x y)) :
    Chain k 0 7 x y := by
  induction k generalizing x y with
  | zero =>
    simp [rootRun] at h
    obtain ⟨hx,hy⟩ := h
    subst x; subst y
    exact Chain.zero 0 7
  | succ k ih =>
    rw [rootRun] at h
    cases he : rootRun k with
    | none => simp [he] at h
    | some s =>
      rcases s with ⟨b,c⟩
      exact Chain.step (ih b c he) (by simpa [he] using h)

theorem root_length (k x y N : Nat) (h : rootRun k=some (.D x y))
    (hx : x+y<2^N) : k≤4*N*N+5*N :=
  chain_length (rootRun_chain k x y h) (by decide) N hx

/-- Any given target is blank-section reachable iff it occurs in the
explicit O(log² mass) bounded prefix. No linear-in-mass enumeration. -/
theorem root_target_iff (x y N : Nat) (hx : x+y<2^N) :
    (∃ k, rootRun k=some (.D x y)) ↔
      ∃ k≤4*N*N+5*N, rootRun k=some (.D x y) := by
  constructor
  · rintro ⟨k,h⟩; exact ⟨k,root_length k x y N h hx,h⟩
  · rintro ⟨k,_,h⟩; exact ⟨k,h⟩

#print axioms chain_path
#print axioms chain_length
#print axioms root_length
#print axioms root_target_iff
#print axioms drain_mass
#print axioms next_two_scale
end BB6.Agent49MassBandSource
