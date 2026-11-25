import Raw40Pump
import Raw40MorePumps
import PartialAudit
import CanonicalRaw114Accepted

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19Raw40
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47PartialAudit
open BB6.Agent31ThreeHole BB6.Agent47CanonicalRefinement BB6.Agent31FourHoleRoster

-- raw40: first 5 rows fixed, seven holes.
def parent : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,3⟩)
  | 3,true => some (some ⟨true,false,0⟩)
  | _,_ => none

theorem parent_root : parent initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem parent_nohalt : weightedTNFNoAssignedHalt parent := by
  intro s; rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> decide

def a0LA : PartialAudit := .split 9 (2,true) (byPartialMove [
  .closed (.cycle 0 12 false (3)),
  .unresolved,
  .closed (.cycle 13 1 false (-1)),
  .closed (.cycle 5 5 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 14 true (-1)),
  .unresolved,
  .closed (.proven pumpTable pump_never),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 5 5 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 14 false (3)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 14 false (3)),
  .unresolved,
  .unresolved])

def a0LB : PartialAudit := .split 11 (1,true) (byPartialMove [
  .closed (.cycle 0 14 false (3)),
  .closed (.cycle 12 8 false (0)),
  .unresolved,
  .closed (.cycle 5 7 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 18 true (-1)),
  .closed (.cycle 9 9 true (0)),
  .unresolved,
  .closed (.cycle 53 1 false (-1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 6 10 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 5 7 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 10 14 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 4 11 false (2)),
  .unresolved,
  .unresolved])

def a0LE : PartialAudit := .split 7 (4,false) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (-1)),
  .closed (.cycle 8 1 false (-2)),
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (-2)),
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved])

def a0LF : PartialAudit := .split 7 (5,false) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (-1)),
  .closed (.cycle 8 1 false (-2)),
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (-2)),
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved])

def a0RB : PartialAudit := .split 7 (1,true) (byPartialMove [
  .unresolved,
  .closed (.cycle 13 8 false (1)),
  .closed (.cycle 9 1 false (1)),
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 7 9 true (1)),
  .unresolved,
  .closed (.cycle 3 11 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 6 4 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 1 9 true (0)),
  .unresolved,
  .closed (.cycle 10 7 true (2)),
  .unresolved,
  .unresolved])

def a0RC : PartialAudit := .split 7 (2,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (1)),
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .closed (.cycle 11 1 false (5)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .closed (.cycle 2 8 true (0)),
  .unresolved,
  .unresolved,
  .unresolved])

def a0RD : PartialAudit := .split 9 (1,true) (byPartialMove [
  .closed (.cycle 11 1 false (1)),
  .closed (.cycle 7 8 false (1)),
  .unresolved,
  .closed (.cycle 7 3 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 14 true (0)),
  .closed (.cycle 7 9 true (0)),
  .unresolved,
  .closed (.cycle 3 13 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 6 4 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 7 3 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 14 true (0)),
  .closed (.cycle 1 11 true (0)),
  .unresolved,
  .closed (.cycle 10 11 true (1)),
  .unresolved,
  .unresolved])

def a0RE : PartialAudit := .split 7 (4,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (1)),
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved])

def a0RF : PartialAudit := .split 7 (5,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (1)),
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved])

def a1LA : PartialAudit := .split 8 (1,true) (byPartialMove [
  .closed (.cycle 6 3 false (0)),
  .closed (.cycle 7 8 false (0)),
  .unresolved,
  .closed (.cycle 7 3 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 18 true (-1)),
  .closed (.cycle 9 9 true (1)),
  .unresolved,
  .closed (.proven RD.table RD.never),
  .unresolved,
  .unresolved,
  .closed (.cycle 6 3 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 7 3 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 6 5 false (1)),
  .closed (.proven RB.table RB.never),
  .unresolved,
  .closed (.cycle 6 5 false (1)),
  .unresolved,
  .unresolved])

def a1LB : PartialAudit := .split 8 (2,true) (byPartialMove [
  .closed (.cycle 6 3 false (0)),
  .unresolved,
  .closed (.cycle 11 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 18 true (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 6 3 false (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved])

def a1LC : PartialAudit := .split 10 (1,true) (byPartialMove [
  .closed (.cycle 6 5 false (0)),
  .closed (.cycle 8 8 false (0)),
  .unresolved,
  .closed (.cycle 8 3 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 26 true (-1)),
  .closed (.cycle 11 9 true (1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 6 5 false (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 8 3 false (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved])

def a1LE : PartialAudit := .split 7 (4,false) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (-1)),
  .closed (.cycle 8 1 false (-2)),
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .closed (.cycle 6 2 true (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (-2)),
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 5 3 false (1)),
  .unresolved,
  .unresolved])

def a1LF : PartialAudit := .split 7 (5,false) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 9 1 false (-1)),
  .closed (.cycle 8 1 false (-2)),
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .closed (.cycle 6 2 true (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 8 1 false (-2)),
  .unresolved,
  .closed (.cycle 7 1 false (-1)),
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 5 3 false (1)),
  .unresolved,
  .unresolved])

def a1RB : PartialAudit := .split 7 (1,true) (byPartialMove [
  .unresolved,
  .closed (.cycle 7 8 false (1)),
  .unresolved,
  .closed (.cycle 7 3 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 7 9 true (1)),
  .unresolved,
  .closed (.cycle 3 11 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 6 2 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 7 3 false (1)),
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .closed (.cycle 1 9 true (0)),
  .unresolved,
  .closed (.cycle 8 7 true (1)),
  .unresolved,
  .unresolved])

def a1RC : PartialAudit := .split 7 (2,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .closed (.cycle 10 1 false (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 6 2 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .closed (.cycle 2 8 true (0)),
  .closed (.cycle 8 7 true (1)),
  .unresolved,
  .unresolved])

def a1RE : PartialAudit := .split 7 (4,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 6 2 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 8 7 true (1)),
  .unresolved,
  .unresolved])

def a1RF : PartialAudit := .split 7 (5,true) (byPartialMove [
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 6 2 true (0)),
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .unresolved,
  .closed (.cycle 0 10 true (0)),
  .unresolved,
  .unresolved,
  .closed (.cycle 8 7 true (1)),
  .unresolved,
  .unresolved])

def tree : PartialAudit := .split 6 (0,true) (byPartialMove [
  a0LA,
  a0LB,
  .closed (.cycle 8 1 false (0)),
  .closed (.cycle 7 1 false (-1)),
  a0LE,
  a0LF,
  .closed (.cycle 0 10 true (0)),
  a0RB,
  a0RC,
  a0RD,
  a0RE,
  a0RF,
  a1LA,
  a1LB,
  a1LC,
  .closed (.cycle 7 1 false (-1)),
  a1LE,
  a1LF,
  .closed (.cycle 0 10 true (0)),
  a1RB,
  a1RC,
  .closed (.cycle 5 2 true (0)),
  a1RE,
  a1RF])

theorem checked : partialCheck 7014 parent tree = true := by decide

def remaining := partialResiduals parent tree

theorem local_sound : ∀ m, compatible parent m → WeightedBound 7014 m ∨
    ∃ e ∈ remaining, compatible e.2 m :=
  partialSound 7014 parent tree parent_root parent_nohalt checked

def holes (p : PartialMachine) : Nat :=
  ((List.finRange 6).flatMap (fun q => [(q,false),(q,true)])).countP (fun s => decide (p s = none))

theorem residual_count : remaining.length = 303 := by decide

theorem residual_mass : (remaining.map (fun e => 25 ^ holes e.2)).sum = 2958984375 := by decide

theorem parent_mass : 25 ^ holes parent = 6103515625 := by decide

theorem parent_in_roster : (BB6.Agent47CanonicalRaw114Accepted.roster.filter (fun e => sameTable e.2 parent)).length = 1 := by decide

#print axioms checked
#print axioms local_sound
#print axioms residual_count
#print axioms residual_mass
#print axioms parent_in_roster
end BB6.Agent19Raw40
