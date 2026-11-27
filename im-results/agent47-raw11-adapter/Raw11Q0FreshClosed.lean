import Raw11Root52CappedParentsConsume
import PhaseTree
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11Q0FreshClosed
open BB6Coverage BB6.Agent13BlankDelay

/-- Coarser q0 targets already closed by the exact first-D cut. The same
    translated cycles are checked again by the original PhaseTree checker. -/
def parent (a c : Move) : PartialMachine := fun s => match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some a)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some c)
  | _,_ => none

def closedRows : List (PartialMachine × BB6.Agent5PhaseTree.Tree) := [
  (parent ⟨true,false,2⟩ ⟨false,false,0⟩, .side 3 5 false (1)),
  (parent ⟨true,false,2⟩ ⟨false,true,0⟩, .side 0 10 true (-1)),
  (parent ⟨true,false,2⟩ ⟨true,true,0⟩, .side 3 2 true (0)),
  (parent ⟨true,false,2⟩ ⟨false,false,2⟩, .side 0 6 false (2)),
  (parent ⟨true,false,2⟩ ⟨false,true,2⟩, .side 0 7 true (0)),
  (parent ⟨true,false,2⟩ ⟨true,false,2⟩, .side 4 6 false (0)),
  (parent ⟨true,false,2⟩ ⟨true,true,2⟩, .side 2 4 true (0)),
  (parent ⟨false,false,2⟩ ⟨false,false,0⟩, .side 0 5 false (2)),
  (parent ⟨false,false,2⟩ ⟨false,true,0⟩, .side 0 5 true (0)),
  (parent ⟨false,false,2⟩ ⟨true,true,0⟩, .side 0 5 true (0))
]

def closedParents : List PartialMachine := closedRows.map Prod.fst

theorem closed_check : closedRows.all (fun x => BB6.Agent5PhaseTree.check 18 x.1 x.2) = true := by decide +kernel

theorem closed_first : closedRows.all (fun x => decide (x.1 initialSlot = some (some ⟨true,true,1⟩))) = true := by decide +kernel

theorem covers (B : Nat) (hB : 18 ≤ B) :
    ∀ p ∈ closedParents, Cover (WeightedBound B) p := by
  intro p hp
  obtain ⟨⟨q,t⟩, hmem, heq⟩ := List.mem_map.mp hp
  change q = p at heq
  subst p
  have hf := of_decide_eq_true (List.all_eq_true.mp closed_first (q,t) hmem)
  have hc := List.all_eq_true.mp closed_check (q,t) hmem
  exact Q0RosterConsume.liftCover hB (.leaf _ (BB6.Agent5PhaseTree.sound 18 q t hf hc))

def closedCodes : List Nat := closedParents.map BB6.Agent47PhaseFrontier.tableCode

def remaining : List PartialMachine :=
  Q0RosterConsume.removeCovered BB6.Agent47Raw11Root52CappedParentsConsume.remaining closedParents

theorem closed_codes_nodup : closedCodes.Nodup := by decide +kernel

theorem closed_codes_in_remaining : ∀ c ∈ closedCodes,
    c ∈ BB6.Agent47Raw11Root52CappedParentsConsume.remainingCodes := by decide +kernel

theorem remaining_exact : remaining.map BB6.Agent47PhaseFrontier.tableCode =
    BB6.Agent47Raw11Root52CappedParentsConsume.remainingCodes.filter (fun c => !(closedCodes.contains c)) := by decide +kernel

theorem remaining_census : (BB6.Agent47Raw11Route.fullRoster.length, remaining.length) = (299,227) := by decide +kernel

theorem cover_from_remaining (B : Nat) (hB : 4663 ≤ B)
    (h : ∀ p ∈ remaining, ∀ m, compatible p m → WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent47Raw11Route.parent := by
  exact BB6.Agent47Raw11Root52CappedParentsConsume.cover_from_remaining B hB
    (Q0RosterConsume.consume B BB6.Agent47Raw11Root52CappedParentsConsume.remaining closedParents
      (covers B (Nat.le_trans (by decide : 18 ≤ 4663) hB)) h)

#print axioms closed_check
#print axioms covers
#print axioms closed_codes_in_remaining
#print axioms remaining_exact
#print axioms remaining_census
#print axioms cover_from_remaining
end BB6.Agent47Raw11Q0FreshClosed
