import CanonicalPartial
import Raw43Data
import Raw43RDData
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent25Raw43Parent
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent8TNFPath

def parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,1⟩)
def tree : PartialAudit := .split 6 (1,true) (byPartialMove [
  .unresolved,
  .closed (.cycle 1 9 true (1)),
  .closed (.cycle 13 1 false (1)),
  .closed (.cycle 10 1 false (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 1 7 true (1)),
  .unresolved,
  .closed (.cycle 1 7 true (1)),
  .split 7 (4,true) (byPartialMove [
    .closed (.cycle 0 8 true (0)),
    .closed (.cycle 1 7 true (1)),
    .closed (.cycle 16 1 false (2)),
    .closed (.cycle 13 1 false (1)),
    .unresolved,
    .unresolved,
    .closed (.cycle 0 8 true (0)),
    .closed (.cycle 1 7 true (1)),
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .unresolved,
    .closed (.cycle 1 9 true (1)),
    .closed (.cycle 13 1 false (1)),
    .unresolved,
    .unresolved,
    .closed (.cycle 0 8 true (0)),
    .closed (.cycle 1 7 true (1)),
    .closed (.cycle 2 6 true (1)),
    .unresolved,
    .unresolved,
    .unresolved]),
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 1 11 true (1)),
  .closed (.cycle 10 1 false (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 1 7 true (1)),
  .unresolved,
  .closed (.cycle 1 7 true (1)),
  .unresolved,
  .unresolved])
theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem parent_nohalt : weightedTNFNoAssignedHalt parent :=
  weightedTNFNoAssignedHalt_refine _ _ _ (pathEnd_nohalt root 2 (path.take 3) firstOneCylinder_no_assigned_halt)
theorem parent_support : TNFSupport parent 4 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck 75 parent 4 tree = true := by decide
def before := canonicalResiduals parent 4 tree
def equalTable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun i => [false,true].all fun b => decide (p (i,b) = q (i,b))
theorem equalTable_sound {p q : PartialMachine} (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨i,b⟩
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hi b hb)
def remaining := before.filter fun e =>
  !(equalTable e.2 BB6.Agent25Raw43.p43child || equalTable e.2 BB6.Agent25Raw43RD.p43child)
theorem before_count : before.length = 23 := by decide
theorem remaining_count : remaining.length = 21 := by decide
theorem root_entries : remaining.all (fun e => decide (e.2 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide
theorem sound (m : Machine) (hm : TNFQuotientCompatible parent m) :
    WeightedBound 75 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases canonicalSound 75 parent 4 tree (by decide) parent_support parent_root parent_nohalt checked m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · by_cases hL : equalTable e.2 BB6.Agent25Raw43.p43child = true
    · rw [equalTable_sound hL] at hq
      exact Or.inl (quotientSafe BB6.Agent25Raw43.p43child_root BB6.Agent25Raw43.all43child m hq)
    · by_cases hR : equalTable e.2 BB6.Agent25Raw43RD.p43child = true
      · rw [equalTable_sound hR] at hq
        have hb := quotientSafe BB6.Agent25Raw43RD.p43child_root BB6.Agent25Raw43RD.all43child m hq
        exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
      · exact Or.inr ⟨e, by simp [remaining,he,hL,hR], hq⟩
theorem cover {B : Nat} (hB : 75 ≤ B)
    (hRest : ∀ e ∈ remaining, Cover (WeightedBound B) e.2) : Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases sound m (compatible_quotient hm) with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hB
  · have hf := of_decide_eq_true (List.all_eq_true.mp root_entries e he)
    exact quotientSafe hf (hRest e he).sound m hq
#print axioms remaining_count
#print axioms sound
#print axioms cover
end BB6.Agent25Raw43Parent
