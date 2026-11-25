import Raw39Data
import Raw39B0RBData
import Raw39B1RCData
import Raw39B0REData
import PartialAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent11Raw39Combined

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent47PartialAudit

abbrev p39 : PartialMachine := BB6.Agent11Raw39.p39

theorem p39_root : p39 initialSlot = some (some ⟨true,true,1⟩) :=
  BB6.Agent11Raw39.p39_root

theorem p39_nohalt : weightedTNFNoAssignedHalt p39 :=
  BB6.Agent11Raw39.p39_nohalt

/-- Raising the weighted threshold preserves every sparse-delay check. -/
theorem weightOK_mono {A B : Nat} (hAB : A ≤ B)
    (p : PartialMachine) (s : Slot) (n : Nat)
    (h : weightOK p s n A = true) : weightOK p s n B = true := by
  unfold weightOK at h ⊢
  apply List.all_eq_true.mpr
  intro d hd
  have hle : d + n + 1 ≤ A := of_decide_eq_true (List.all_eq_true.mp h d hd)
  exact decide_eq_true_eq.mpr (Nat.le_trans hle hAB)

/-- The exact first-hole predicate is monotone in its weighted bound. -/
theorem zipQueryOK_mono {A B : Nat} (hAB : A ≤ B)
    (p : PartialMachine) (n : Nat) (s : Slot)
    (h : zipQueryOK A p n s = true) : zipQueryOK B p n s = true := by
  unfold zipQueryOK at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  rcases h with ⟨hread, hrest⟩
  rcases hrest with ⟨hhole, hweight⟩
  exact ⟨hread, ⟨hhole, weightOK_mono hAB p s n hweight⟩⟩

/-- Every closed Audit remains closed when its score threshold increases. -/
theorem zipCheck_mono {A B : Nat} (hAB : A ≤ B)
    (p : PartialMachine) (t : Audit)
    (h : zipCheck A p t = true) : zipCheck B p t = true := by
  induction t generalizing p with
  | last n s =>
      simp only [zipCheck, Bool.and_eq_true] at h ⊢
      exact ⟨zipQueryOK_mono hAB p n s h.1, h.2⟩
  | cycle e k r b =>
      simpa [zipCheck] using h
  | far rev d C =>
      simpa [zipCheck] using h
  | proven q safe =>
      simpa [zipCheck] using h
  | split n s kids ih =>
      simp only [zipCheck, Bool.and_eq_true] at h ⊢
      refine ⟨zipQueryOK_mono hAB p n s h.1, ?_⟩
      apply allMoves_of _
      intro mv
      exact ih mv (refine p s (some mv)) (allMoves_sound _ h.2 mv)

/-- The same monotonicity holds for partial coverage trees. -/
theorem partialCheck_mono {A B : Nat} (hAB : A ≤ B)
    (p : PartialMachine) (t : PartialAudit)
    (h : partialCheck A p t = true) : partialCheck B p t = true := by
  induction t generalizing p with
  | unresolved => rfl
  | closed tree => exact zipCheck_mono hAB p tree h
  | split n s kids ih =>
      simp only [partialCheck, Bool.and_eq_true] at h ⊢
      refine ⟨zipQueryOK_mono hAB p n s h.1, ?_⟩
      apply allMoves_of _
      intro mv
      exact ih mv (refine p s (some mv)) (allMoves_sound _ h.2 mv)

/-- Lift the four independently source-checked child certificates to the
    common parent threshold 1882. -/
theorem child0RB_checked :
    zipCheck 1882 (refine p39 (0,true) (some ⟨false,true,1⟩))
      BB6.Agent11Raw39B0RB.treeChild = true := by
  have h := zipCheck_mono (A := 1271) (B := 1882) (by decide)
    BB6.Agent11Raw39B0RB.pChild
    BB6.Agent11Raw39B0RB.treeChild
    BB6.Agent11Raw39B0RB.treeChild_checked
  simpa [p39, BB6.Agent11Raw39B0RB.pChild, BB6.Agent11Raw39B0RB.p39] using h

theorem child1RB_checked :
    zipCheck 1882 (refine p39 (0,true) (some ⟨true,true,1⟩))
      BB6.Agent11Raw39.tree1RB = true := by
  have h := zipCheck_mono (A := 175) (B := 1882) (by decide)
    BB6.Agent11Raw39.p1RB
    BB6.Agent11Raw39.tree1RB
    BB6.Agent11Raw39.tree1RB_checked
  simpa [p39, BB6.Agent11Raw39.p1RB, BB6.Agent11Raw39.p39] using h

theorem child1RC_checked :
    zipCheck 1882 (refine p39 (0,true) (some ⟨true,true,2⟩))
      BB6.Agent11Raw39B1RC.treeChild = true := by
  simpa [p39, BB6.Agent11Raw39B1RC.pChild, BB6.Agent11Raw39B1RC.p39] using
    BB6.Agent11Raw39B1RC.treeChild_checked

theorem child0RE_checked :
    zipCheck 1882 (refine p39 (0,true) (some ⟨false,true,4⟩))
      BB6.Agent11Raw39B0RE.treeChild = true := by
  have h := zipCheck_mono (A := 944) (B := 1882) (by decide)
    BB6.Agent11Raw39B0RE.pChild
    BB6.Agent11Raw39B0RE.treeChild
    BB6.Agent11Raw39B0RE.treeChild_checked
  simpa [p39, BB6.Agent11Raw39B0RE.pChild, BB6.Agent11Raw39B0RE.p39] using h

theorem query39 : zipQueryOK 1882 p39 6 (0,true) = true := by
  simpa [p39, BB6.Agent11Raw39B1RC.p39] using BB6.Agent11Raw39B1RC.query39

/-- The parent split retains all unproved children explicitly. Four children
    are closed by source-checked certificates; nine more are cycle-closed. -/
def partialKids : Move → PartialAudit := byPartialMove [
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 13 1 false (1)),
  .closed (.cycle 10 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 8 true (0)),
  .closed BB6.Agent11Raw39B0RB.treeChild,
  .unresolved,
  .closed (.cycle 0 8 true (0)),
  .closed BB6.Agent11Raw39B0RE.treeChild,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 12 true (0)),
  .closed (.cycle 10 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 8 true (0)),
  .closed BB6.Agent11Raw39.tree1RB,
  .closed BB6.Agent11Raw39B1RC.treeChild,
  .closed (.cycle 0 8 true (0)),
  .unresolved,
  .unresolved]

def partialTree : PartialAudit := .split 6 (0,true) partialKids

theorem partialKids_checked (mv : Move) :
    partialCheck 1882 (refine p39 (0,true) (some mv)) (partialKids mv) = true := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact child0RB_checked
  · decide
  · exact child1RB_checked
  · decide
  · decide
  · decide
  · exact child1RC_checked
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact child0RE_checked
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem partialTree_checked : partialCheck 1882 p39 partialTree = true := by
  change (zipQueryOK 1882 p39 6 (0,true) &&
    allMoves (fun mv => partialCheck 1882 (refine p39 (0,true) (some mv)) (partialKids mv))) = true
  simp only [Bool.and_eq_true]
  exact ⟨query39, allMoves_of _ partialKids_checked⟩

def residuals := partialResiduals p39 partialTree

theorem residual_count : residuals.length = 11 := by decide

/-- Every completion of the Raw39 parent is either bounded by 1882 or lies
    in one of the eleven explicitly retained residual cylinders. -/
theorem cut_sound : ∀ m, compatible p39 m →
    WeightedBound 1882 m ∨ ∃ e ∈ residuals, compatible e.2 m :=
  partialSound 1882 p39 partialTree p39_root p39_nohalt partialTree_checked

#print axioms cut_sound
#print axioms residual_count

end BB6.Agent11Raw39Combined
