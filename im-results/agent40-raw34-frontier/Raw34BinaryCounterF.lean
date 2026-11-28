import Raw34BinaryCounter
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34BinaryCounterF
open BB6Coverage BB6.Agent13BlankDelay

/-!
Swap the inactive E and F control labels in the original-source
binary-counter nonhalting theorem to obtain a genuinely separate
D1=1RF five-hole Raw34 child:
  1RB---_1RC---_0RD0LC_1LC1RF_------_1RD---
This is exact state conjugacy, not a new simulation.
-/

def pf : PartialMachine := fun slot =>
  match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def ef : StatePerm := swapStates (4 : Fin 6) 5

def permPartial (p : PartialMachine) : PartialMachine := fun slot =>
  (p (ef.backward slot.1,slot.2)).map (Option.map (renameMove ef))

theorem source_eq_perm :
    BB6.Agent40Raw34BinaryCounter.p = permPartial pf := by
  funext slot
  rcases slot with ⟨s,b⟩
  fin_cases s <;> cases b <;>
    rfl

theorem perm_compatible (m : Machine) (hm : compatible pf m) :
    compatible (permPartial pf) (renameTable ef m) := by
  intro slot target hp
  unfold permPartial at hp
  cases hs : pf (ef.backward slot.1,slot.2) with
  | none => simp [hs] at hp
  | some v =>
    have hm' := hm (ef.backward slot.1,slot.2) v hs
    simpa [renameTable,hs,hm'] using hp

theorem renamed_compatible (m : Machine) (hm : compatible pf m) :
    compatible BB6.Agent40Raw34BinaryCounter.p (renameTable ef m) := by
  rw [source_eq_perm]
  exact perm_compatible m hm

theorem all_time_never (m : Machine) (hm : compatible pf m) :
    NeverHalts m := by
  intro n
  have hz : ef.forward 0 = 0 := by decide
  have hb : renameConfig ef blank = blank := by
    simp [renameConfig,blank,hz]
  have hr := rename_run ef m blank n
  rw [hb] at hr
  have hLive := BB6.Agent40Raw34BinaryCounter.all_time_never
    (renameTable ef m) (renamed_compatible m hm) n
  rw [hr] at hLive
  cases hc : run m n blank with
  | none => simp [hc] at hLive
  | some c => rfl

#print axioms source_eq_perm
#print axioms perm_compatible
#print axioms renamed_compatible
#print axioms all_time_never
end BB6.Agent40Raw34BinaryCounterF
