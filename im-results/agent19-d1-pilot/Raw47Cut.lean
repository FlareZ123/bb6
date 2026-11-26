import CanonicalPartial

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw47Cut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

/-- D1=0RC sibling of the authentic firstOneCylinder path. -/
def parent : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | _,_ => none

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

theorem parent_support : TNFSupport parent 4 := supportOK_sound _ _ (by decide)

def tree : PartialAudit :=
.split 6 (2,true) (byPartialMove [
.split 10 (0,true) (byPartialMove [
.closed (.cycle 0 13 false (3)),
.unresolved,
.closed (.cycle 14 1 false (0)),
.closed (.cycle 24 1 false (2)),
.unresolved,
.unresolved,
.closed (.cycle 0 11 true (0)),
.closed (.cycle 1 10 true (1)),
.closed (.cycle 5 31 true (1)),
.closed (.cycle 3 8 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 18 1 false (4)),
.closed (.cycle 0 13 true (0)),
.unresolved,
.unresolved,
.closed (.cycle 0 11 true (0)),
.closed (.cycle 1 10 true (1)),
.closed (.cycle 2 9 true (1)),
.closed (.cycle 0 14 true (0)),
.unresolved,
.unresolved
]),
.closed (.cycle 5 14 true (1)),
.closed (.cycle 13 1 false (1)),
.closed (.cycle 10 1 false (0)),
.split 7 (4,false) (byPartialMove [
.unresolved,
.unresolved,
.closed (.cycle 11 1 false (-1)),
.closed (.cycle 10 1 false (2)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 28 1 false (6)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 17 1 false (5)),
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 14 true (1)),
.closed (.cycle 4 4 true (1)),
.unresolved,
.unresolved
]),
.unresolved,
.split 7 (0,true) (byPartialMove [
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 16 1 false (2)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 0 20 true (0)),
.closed (.cycle 0 17 true (0)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 0 10 true (0)),
.closed (.cycle 0 26 true (0)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 0 11 true (0)),
.unresolved,
.unresolved
]),
.split 7 (1,true) (byPartialMove [
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 16 1 false (2)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 28 1 false (10)),
.closed (.cycle 24 1 false (8)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 9 true (1)),
.closed (.cycle 36 1 false (10)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 1 10 true (1)),
.unresolved,
.unresolved
]),
.closed (.cycle 21 1 false (7)),
.closed (.cycle 20 1 false (6)),
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
.unresolved,
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.unresolved,
.unresolved,
.unresolved
]),
.unresolved,
.split 8 (1,true) (byPartialMove [
.unresolved,
.closed (.cycle 9 9 false (1)),
.unresolved,
.closed (.cycle 36 1 false (6)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 9 true (1)),
.closed (.cycle 6 14 true (1)),
.closed (.cycle 5 14 true (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 4 true (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 9 true (1)),
.unresolved,
.closed (.cycle 18 5 true (4)),
.unresolved,
.unresolved
]),
.split 9 (1,true) (byPartialMove [
.unresolved,
.closed (.cycle 175 92 false (-1)),
.closed (.cycle 15 1 false (-1)),
.closed (.cycle 17 1 false (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 11 true (1)),
.closed (.cycle 6 4 true (1)),
.closed (.cycle 49 1 false (7)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 10 3 false (0)),
.closed (.cycle 10 6 true (-2)),
.closed (.cycle 15 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 1 11 true (1)),
.closed (.cycle 8 2 true (1)),
.closed (.cycle 5 20 true (1)),
.unresolved,
.unresolved
]),
.closed (.cycle 35 1 false (7)),
.closed (.cycle 10 1 false (0)),
.split 7 (4,false) (byPartialMove [
.unresolved,
.unresolved,
.closed (.cycle 11 1 false (-1)),
.closed (.cycle 13 1 false (1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 6 2 true (1)),
.closed (.cycle 35 1 false (7)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 8 4 true (-2)),
.closed (.cycle 11 1 false (-1)),
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 5 14 true (1)),
.unresolved,
.unresolved
]),
.unresolved,
.split 7 (0,true) (byPartialMove [
.closed (.cycle 0 9 true (0)),
.unresolved,
.closed (.cycle 0 9 true (0)),
.closed (.cycle 0 21 true (0)),
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
.unresolved
]),
.split 7 (1,true) (byPartialMove [
.unresolved,
.closed (.cycle 1 8 true (1)),
.closed (.cycle 1 8 true (1)),
.closed (.cycle 1 20 true (0)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 1 15 true (1)),
.closed (.cycle 3 5 true (1)),
.unresolved,
.unresolved,
.unresolved,
.closed (.cycle 12 5 false (2)),
.closed (.cycle 6 2 true (2)),
.closed (.cycle 1 9 true (1)),
.unresolved,
.unresolved,
.closed (.cycle 0 8 true (0)),
.closed (.cycle 1 7 true (1)),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 1 10 true (1)),
.unresolved,
.unresolved
]),
.closed (.cycle 2 6 true (1)),
.closed (.cycle 14 3 true (4)),
.split 7 (4,true) (byPartialMove [
.unresolved,
.unresolved,
.unresolved,
.unresolved,
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
.unresolved
]),
.unresolved
])

theorem canonical_checked : canonicalCheck 7014 parent 4 tree = true := by decide

def canonicalRemaining := canonicalResiduals parent 4 tree

theorem canonical_count : canonicalRemaining.length = 114 := by decide

/-- Exact source-sound refinement: every compatible completion is bounded or belongs to one of the listed open leaves. -/
theorem canonical_local_sound : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 7014 m ∨ ∃ e ∈ canonicalRemaining, TNFQuotientCompatible e.2 m :=
  canonicalSound 7014 parent 4 tree (by decide) parent_support parent_root parent_nohalt canonical_checked

theorem canonical_checked_84 : canonicalCheck 84 parent 4 tree = true := by decide

/-- Stronger root-compatible local bound, matching Agent 50's 84-step root frontier. -/
theorem canonical_local_sound_84 : ∀ m, TNFQuotientCompatible parent m →
    WeightedBound 84 m ∨ ∃ e ∈ canonicalRemaining, TNFQuotientCompatible e.2 m :=
  canonicalSound 84 parent 4 tree (by decide) parent_support parent_root parent_nohalt canonical_checked_84

#print axioms canonical_checked
#print axioms canonical_checked_84
#print axioms canonical_local_sound_84
#print axioms canonical_count
#print axioms canonical_local_sound
end BB6.Agent19Raw47Cut
