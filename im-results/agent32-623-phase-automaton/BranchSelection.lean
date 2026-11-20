import Lean
import DrainDigitTransducerCarry

/-
# Conditional #623 output-branch reduction

This file formalizes the conditional arithmetic lemma in
'communications/broadcast/20261120T065842Z_Critic-623-root-phase-induction.md'
and 'im-results/agent32-623-phase-automaton/BranchSelection.md'. It uses
the four sector relations and exact threshold offsets from that note.

The hypotheses include the nonterminal-window condition and the depth
bounds on D and R. This file does not prove those hypotheses along the
authentic blank-root orbit, does not import the original source cocycle,
and is not a #623 nonhalting theorem.

Checked with Lean 4.36.0-rc2 and warnings treated as errors.
-/

namespace BB6Root623BranchSelection

inductive Sector where
  | LO | LE | RO | RE
  deriving DecidableEq, Repr

def thresholdOffset : Sector → Int
  | .LO => 19
  | .LE => 10
  | .RO => -4
  | .RE => 2

def sectorRelation (s : Sector) (g h : Int) : Prop :=
  match s with
  | .LO => h = g - 9
  | .LE => h = g - 5
  | .RO => g = 2*h + 1
  | .RE => g = 2*h + 2

theorem thresholdOffset_bounds (s : Sector) :
    -19 ≤ thresholdOffset s ∧ thresholdOffset s ≤ 19 := by
  cases s <;> decide

theorem g_far_of_h_far (s : Sector) (ell g h : Int)
    (hrel : sectorRelation s g h)
    (hfar : h > 9*ell+22 ∨ h < -(9*ell+22)) :
    g > 9*ell+13 ∨ g < -(9*ell+13) := by
  cases s <;> simp [sectorRelation] at hrel <;>
    rcases hfar with hp | hn <;> omega

theorem threshold_bounds (ell D R c : Int)
    (hell : 3 ≤ ell)
    (hDlo : -(ell+1) ≤ D) (hDhi : D ≤ ell+1)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell)
    (hclo : -19 ≤ c) (hchi : c ≤ 19) :
    -(5*ell+22) ≤ 3*D+2*R+c ∧ 3*D+2*R+c ≤ 5*ell+22 := by
  have hDlo3 : -3*(ell+1) ≤ 3*D := by
    calc
      -3*(ell+1) = 3*-(ell+1) := Int.neg_mul_comm 3 (ell+1)
      _ ≤ 3*D := Int.mul_le_mul_of_nonneg_left hDlo (show (0:Int) ≤ 3 by decide)
  have hDhi3 : 3*D ≤ 3*(ell+1) :=
    Int.mul_le_mul_of_nonneg_left hDhi (show (0:Int) ≤ 3 by decide)
  have hRlo2 : 0 ≤ 2*R := Int.mul_nonneg (show (0:Int) ≤ 2 by decide) hRlo
  have hRhi2 : 2*R ≤ 2*ell :=
    Int.mul_le_mul_of_nonneg_left hRhi (show (0:Int) ≤ 2 by decide)
  constructor
  · calc
      -(5*ell+22) ≤ -3*(ell+1)-19 := by omega
      _ ≤ 3*D+2*R+c := by omega
  · calc
      3*D+2*R+c ≤ 3*(ell+1)+2*ell+19 := by omega
      _ = 5*ell+22 := by omega

theorem sign_branch_reduction (ell g T : Int)
    (hell : 3 ≤ ell)
    (hfar : g > 9*ell+13 ∨ g < -(9*ell+13))
    (hT : -(5*ell+22) ≤ T ∧ T ≤ 5*ell+22) :
    (g ≥ T) ↔ (g > 0) := by
  rcases hfar with hp | hn
  · have hgt : T < g := by omega
    constructor <;> intro _ <;> omega
  · have hlt : g < T := by omega
    constructor <;> intro _ <;> omega

theorem output_left_iff_positive_g (s : Sector) (ell g h D R : Int)
    (hell : 3 ≤ ell)
    (hrel : sectorRelation s g h)
    (hfar : h > 9*ell+22 ∨ h < -(9*ell+22))
    (hDlo : -(ell+1) ≤ D) (hDhi : D ≤ ell+1)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell) :
    (g ≥ 3*D+2*R+thresholdOffset s) ↔ (g > 0) := by
  have hg := g_far_of_h_far s ell g h hrel hfar
  have hc := thresholdOffset_bounds s
  have hT := threshold_bounds ell D R (thresholdOffset s) hell
    hDlo hDhi hRlo hRhi hc.1 hc.2
  exact sign_branch_reduction ell g (3*D+2*R+thresholdOffset s) hell hg hT

theorem output_right_iff_negative_g (s : Sector) (ell g h D R : Int)
    (hell : 3 ≤ ell)
    (hrel : sectorRelation s g h)
    (hfar : h > 9*ell+22 ∨ h < -(9*ell+22))
    (hDlo : -(ell+1) ≤ D) (hDhi : D ≤ ell+1)
    (hRlo : 0 ≤ R) (hRhi : R ≤ ell) :
    (g < 3*D+2*R+thresholdOffset s) ↔ (g < 0) := by
  have hleft := output_left_iff_positive_g s ell g h D R
    hell hrel hfar hDlo hDhi hRlo hRhi
  have hgfar := g_far_of_h_far s ell g h hrel hfar
  have hnonzero : g ≠ 0 := by
    rcases hgfar with hp | hn <;> omega
  constructor
  · intro hright
    have hnotleft : ¬ g ≥ 3*D+2*R+thresholdOffset s := by omega
    have hnotpos : ¬ g > 0 := by
      intro hg
      exact hnotleft (hleft.mpr hg)
    omega
  · intro hneg
    have hnotpos : ¬ g > 0 := by omega
    have hnotleft : ¬ g ≥ 3*D+2*R+thresholdOffset s := by
      intro hleft'
      exact hnotpos (hleft.mp hleft')
    omega


/-- The exact depth statistics produced by the imported drain transducer. -/
def sourceDepthStats (L b : Nat) : DrainStats :=
  runStats L (b % 3^L) DrainState.A

def sourceDepthD (L b : Nat) : Int :=
  weightedD L (sourceDepthStats L b)

def sourceDepthR (L b : Nat) : Int :=
  weightedR (sourceDepthStats L b)

/-- Source-derived wrapper: |D|≤L+1 and 0≤R≤L follow from the imported
runStats_weight_bounds theorem, rather than being free hypotheses. -/
theorem sourceDepth_bounds (L b : Nat) :
    -(Int.ofNat L+1) ≤ sourceDepthD L b ∧
    sourceDepthD L b ≤ Int.ofNat L+1 ∧
    0 ≤ sourceDepthR L b ∧
    sourceDepthR L b ≤ Int.ofNat L := by
  let stats := sourceDepthStats L b
  have h := runStats_weight_bounds L (b % 3^L) DrainState.A
  change 0 ≤ weightedE stats ∧ weightedE stats ≤ weightedR stats ∧
    weightedR stats ≤ Int.ofNat L at h
  change -(Int.ofNat L+1) ≤ weightedD L stats ∧
    weightedD L stats ≤ Int.ofNat L+1 ∧
    0 ≤ weightedR stats ∧ weightedR stats ≤ Int.ofNat L
  simp only [weightedD, weightedE, weightedR] at h ⊢
  omega

/-- Branch selection with the depth bounds discharged by the imported
three-state drain transducer. The outside-window and sector-phase
hypotheses remain root-orbit obligations. -/
theorem output_left_iff_positive_g_from_drain (s : Sector) (L b : Nat)
    (g h : Int)
    (hL : 3 ≤ L)
    (hrel : sectorRelation s g h)
    (hfar : h > 9*Int.ofNat L+22 ∨ h < -(9*Int.ofNat L+22)) :
    (g ≥ 3*sourceDepthD L b+2*sourceDepthR L b+thresholdOffset s) ↔
      (g > 0) := by
  have hd := sourceDepth_bounds L b
  have hLInt : 3 ≤ Int.ofNat L := by
    have hcast := Int.ofNat_le.mpr hL
    simpa using hcast
  exact output_left_iff_positive_g s (Int.ofNat L) g h
    (sourceDepthD L b) (sourceDepthR L b) hLInt hrel hfar
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

theorem output_right_iff_negative_g_from_drain (s : Sector) (L b : Nat)
    (g h : Int)
    (hL : 3 ≤ L)
    (hrel : sectorRelation s g h)
    (hfar : h > 9*Int.ofNat L+22 ∨ h < -(9*Int.ofNat L+22)) :
    (g < 3*sourceDepthD L b+2*sourceDepthR L b+thresholdOffset s) ↔
      (g < 0) := by
  have hd := sourceDepth_bounds L b
  have hLInt : 3 ≤ Int.ofNat L := by
    have hcast := Int.ofNat_le.mpr hL
    simpa using hcast
  exact output_right_iff_negative_g s (Int.ofNat L) g h
    (sourceDepthD L b) (sourceDepthR L b) hLInt hrel hfar
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

#print axioms thresholdOffset_bounds
#print axioms output_left_iff_positive_g
#print axioms output_right_iff_negative_g
#print axioms sourceDepth_bounds
#print axioms output_left_iff_positive_g_from_drain
#print axioms output_right_iff_negative_g_from_drain

end BB6Root623BranchSelection

#print axioms BB6Root623BranchSelection.g_far_of_h_far
#print axioms BB6Root623BranchSelection.threshold_bounds
#print axioms BB6Root623BranchSelection.sign_branch_reduction
