import CanonicalPartial
import Raw49Sweep
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent7Raw49Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot
open BB6.Agent7Raw49Sweep (Kind)

def parent : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,true,2⟩)
  | _,_ => none

def tree : PartialAudit := .split 6 (2,true) (byPartialMove [
.split 7 (0,true) (byPartialMove [
.closed (.cycle 0 9 false (3)),
.unresolved,
.closed (.cycle 0 9 false (3)),
.closed (.cycle 15 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 10 true (1)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 6 5 false (2)),
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 10 true (1)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 4 4 true (1)),
.unresolved,
.unresolved]),
.split 7 (1,true) (byPartialMove [
.unresolved,
.closed (.cycle 8 7 false (1)),
.closed (.cycle 17 1 false (-1)),
.closed (.cycle 15 1 false (-1)),
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (0)),
.closed (.cycle 1 10 true (1)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 3 false (0)),
.closed (.cycle 10 10 true (0)),
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (0)),
.closed (.cycle 1 10 true (1)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 4 4 true (1)),
.unresolved,
.unresolved]),
.closed (.cycle 10 1 false (0)),
.closed (.cycle 2 8 true (1)),
.split 7 (4,true) (byPartialMove [
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 15 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 10 true (1)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 10 true (1)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 4 4 true (1)),
.unresolved,
.unresolved]),
.unresolved,
.split 7 (0,true) (byPartialMove [
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 0 11 true (0)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.unresolved,
.closed (.cycle 2 13 true (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (0)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 4 4 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 0 11 true (0)),
.unresolved,
.unresolved]),
.split 7 (1,true) (byPartialMove [
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 1 10 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.unresolved,
.closed (.cycle 2 13 true (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 9 true (1)),
.closed (.cycle 2 8 true (1)),
.closed (.cycle 4 4 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 1 10 true (1)),
.unresolved,
.unresolved]),
.unresolved,
.closed (.cycle 2 6 true (1)),
.split 7 (4,true) (byPartialMove [
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.unresolved,
.closed (.cycle 2 13 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 2 8 true (1)),
.closed (.cycle 4 4 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved,
.split 7 (0,true) (byPartialMove [
.closed (.cycle 0 22 false (3)),
.unresolved,
.unresolved,
.closed (.cycle 17 1 false (-1)),
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (0)),
.unresolved,
.unresolved,
.closed (.cycle 2 10 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (0)),
.unresolved,
.closed (.cycle 6 2 true (1)),
.closed (.cycle 2 10 true (1)),
.unresolved,
.unresolved]),
.split 7 (1,true) (byPartialMove [
.unresolved,
.closed (.cycle 23 14 true (0)),
.closed (.cycle 13 1 false (-1)),
.closed (.cycle 17 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 9 true (1)),
.closed (.cycle 6 4 true (1)),
.closed (.cycle 2 10 true (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 3 false (0)),
.closed (.cycle 10 4 true (-2)),
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 9 true (1)),
.closed (.cycle 6 2 true (1)),
.closed (.cycle 2 10 true (1)),
.unresolved,
.unresolved]),
.closed (.cycle 7 4 true (-1)),
.closed (.cycle 5 2 true (1)),
.split 7 (4,true) (byPartialMove [
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 17 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 2 10 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 6 2 true (1)),
.closed (.cycle 2 10 true (1)),
.unresolved,
.unresolved]),
.unresolved,
.split 7 (0,true) (byPartialMove [
.closed (.cycle 0 11 false (3)),
.unresolved,
.closed (.cycle 0 9 true (0)),
.closed (.cycle 2 7 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 0 16 true (0)),
.closed (.cycle 3 5 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 6 2 true (2)),
.closed (.cycle 0 10 true (0)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 0 11 true (0)),
.unresolved,
.unresolved]),
.split 7 (1,true) (byPartialMove [
.unresolved,
.closed (.cycle 8 9 false (2)),
.closed (.cycle 1 8 true (1)),
.closed (.cycle 2 7 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 1 15 true (1)),
.closed (.cycle 3 5 true (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 5 false (2)),
.closed (.cycle 6 2 true (2)),
.closed (.cycle 1 9 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 1 10 true (1)),
.unresolved,
.unresolved]),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 2 6 true (1)),
.split 7 (4,true) (byPartialMove [
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 2 7 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.unresolved,
.closed (.cycle 3 5 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 6 2 true (2)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.unresolved,
.unresolved,
.unresolved]),
.unresolved])

theorem root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide
theorem nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem supported : TNFSupport parent 4 := supportOK_sound _ _ (by decide)
theorem checked : canonicalCheck 7014 parent 4 tree = true := by decide

def equalTable (p q : PartialMachine) : Bool := (List.finRange 6).all fun i => [false,true].all fun b => decide (p (i,b) = q (i,b))
theorem equalTable_sound {p q : PartialMachine} (h : equalTable p q = true) : p = q := by
  funext s
  rcases s with ⟨i,b⟩
  have hi := List.all_eq_true.mp h i (List.mem_finRange i)
  have hb : b ∈ [false,true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hi b hb)

def kinds : List Kind := [.direct,.viaA,.viaB,.viaE]
def sweepMatch (p : PartialMachine) : Bool := kinds.any (fun k => equalTable p (BB6.Agent7Raw49Sweep.table k))
def remaining := (canonicalResiduals parent 4 tree).filter (fun e => !sweepMatch e.2)

theorem original_count : (canonicalResiduals parent 4 tree).length = 125 := by decide
theorem remaining_count : remaining.length = 121 := by decide

theorem sweepWeighted (k : Kind) (m : Machine) (hm : compatible (BB6.Agent7Raw49Sweep.table k) m) : WeightedBound 7014 m := by
  intro n d hn hd
  have h := BB6.Agent7Raw49Sweep.never k m hm (n+1)
  rw [hn.2] at h
  contradiction

theorem sweepRoot (k : Kind) : BB6.Agent7Raw49Sweep.table k initialSlot = some (some ⟨true,true,1⟩) := by cases k <;> decide

theorem parent_cut (m : Machine) (hm : TNFQuotientCompatible parent m) : WeightedBound 7014 m ∨ ∃ e ∈ remaining, TNFQuotientCompatible e.2 m := by
  rcases canonicalSound 7014 parent 4 tree (by decide) supported root nohalt checked m hm with h | ⟨e,he,hq⟩
  · exact Or.inl h
  · cases hh : sweepMatch e.2 with
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hh]⟩,hq⟩
    | true =>
      obtain ⟨k,hk,hmatch⟩ := List.any_eq_true.mp hh
      have heq := equalTable_sound hmatch
      rw [heq] at hq
      exact Or.inl (quotientSafe (sweepRoot k) (sweepWeighted k) m hq)

#print axioms parent_cut
#print axioms remaining_count
end BB6.Agent7Raw49Cut
