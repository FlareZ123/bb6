import Raw391LEBase
import ExactAuditWeight
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot BB6.Agent10ZipAudit BB6.Agent10CachedAudit BB6.Agent31ThreeHole BB6.Agent10ExactAuditWeight
open BB6Coverage.Agent10ZipAudit BB6.Agent11SemanticChunks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent43Raw391LELate

def table : PartialMachine := fun s => match s.1.val,s.2 with
 | 0,false => some (some ⟨true,true,1⟩)
 | 0,true => some (some ⟨true,false,4⟩)
 | 1,false => some (some ⟨true,true,2⟩)
 | 1,true => some (some ⟨true,false,5⟩)
 | 2,false => some (some ⟨false,true,3⟩)
 | 2,true => some (some ⟨true,true,1⟩)
 | 3,false => some (some ⟨true,false,3⟩)
 | 3,true => some (some ⟨false,true,0⟩)
 | 4,false => some (some ⟨false,false,0⟩)
 | 4,true => some (some ⟨false,false,1⟩)
 | 5,true => some (some ⟨true,true,3⟩)
 | _,_ => none

theorem actualDelays : possibleDelays (refine table (5,false) none) 0 = [0,1] := by decide

theorem insufficient : weightOK table (5,false) 28309 28310 = false := by decide

theorem readHole : zipRead table 28309 = some (5,false) := by decide +kernel

theorem query : zipQueryOK 28311 table 28309 (5,false) = true := by
  unfold zipQueryOK
  rw [readHole]
  rfl

theorem not_bound : ¬ Bound 28310 table := by
  intro h
  have H := query_weight_necessary (by decide : table initialSlot = some (some ⟨true,true,1⟩)) query h
  rw [insufficient] at H
  contradiction

theorem bound_28311 : Bound 28311 table := by
  apply bound_of_check 28311 table (.last 28309 (5,false)) (by decide)
  change zipQueryOK 28311 table 28309 (5,false) && restOK table (5,false) = true
  rw [query]
  decide

theorem parent_not_bound : ¬ Bound 28310 BB6.Agent11Raw391LE.pChild := by
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
#print axioms bound_28311
end BB6.Agent43Raw391LELate
