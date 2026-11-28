import Raw39SemanticChunks
import ExactAuditWeight
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent10CachedAudit BB6.Agent31ThreeHole BB6.Agent10ExactAuditWeight
open BB6Coverage.Agent10ZipAudit BB6.Agent11SemanticChunks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw390LELate

abbrev p39 : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,true,0⟩)
abbrev pChild : PartialMachine := refine p39 (0,true) (some ⟨false,false,4⟩)

def table : PartialMachine := fun s => match s.1.val,s.2 with
 | 0,false => some (some ⟨true,true,1⟩)
 | 0,true => some (some ⟨false,false,4⟩)
 | 1,false => some (some ⟨true,true,2⟩)
 | 1,true => some (some ⟨false,false,0⟩)
 | 2,false => some (some ⟨false,true,3⟩)
 | 3,false => some (some ⟨true,false,3⟩)
 | 3,true => some (some ⟨false,true,0⟩)
 | 4,false => some (some ⟨true,true,0⟩)
 | 4,true => some (some ⟨true,false,5⟩)
 | 5,false => some (some ⟨false,false,1⟩)
 | 5,true => some (some ⟨true,false,5⟩)
 | _,_ => none

theorem actualDelays : possibleDelays (refine table (2,true) none) 0 = [0] := by decide

theorem insufficient : weightOK table (2,true) 15124 15124 = false := by decide

theorem readHole : zipRead table 15124 = some (2,true) := by decide +kernel

theorem query : zipQueryOK 15125 table 15124 (2,true) = true := by
  unfold zipQueryOK
  rw [readHole]
  rfl

theorem not_bound : ¬ Bound 15124 table := by
  intro h
  have H := query_weight_necessary (by decide : table initialSlot = some (some ⟨true,true,1⟩)) query h
  rw [insufficient] at H
  contradiction

theorem bound_15125 : Bound 15125 table := by
  apply bound_of_check 15125 table (.last 15124 (2,true)) (by decide)
  change zipQueryOK 15125 table 15124 (2,true) && restOK table (2,true) = true
  rw [query]
  decide

theorem parent_not_bound : ¬ Bound 15124 pChild := by
  intro h
  apply not_bound
  intro m hm
  apply h m
  intro s t hs
  apply hm s t
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;> cases b <;> first | exact hs | contradiction

#print axioms parent_not_bound
#print axioms not_bound
#print axioms bound_15125
end BB6.Agent43Raw390LELate
