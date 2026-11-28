import Raw34TripleSweepGrowth
import Raw34AlternatingGrowth
import WeightedTNF
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Two new six-state Raw34 polynomial-growth, genuinely never-halting
physical cylinders from an exact E/F permutation of previously proved
sweep-pump invariants. This is source-theorem transport, not an
experimental simulator recurrence.

F-triple sweep:
  1RB---_1RC---_0RD0RF_1LC1RD_------_---1LD
F alternating sweep:
  1RB---_1RC---_0RD0LD_1LC0RF_------_1RD---
They are not covered by finite translated-cycle inference: tape length
grows without bound. Every other unknown slot may be HALT.
-/
namespace BB6.Agent40Raw34ConjugateGrowth
open BB6Coverage BB6.Agent13BlankDelay

def tripleF : PartialMachine := fun slot =>
  match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,true,5⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,true,3⟩)
  | 5,true  => some (some ⟨true,false,3⟩)
  | _,_ => none

def alternatingF : PartialMachine := fun slot =>
  match slot.1.val,slot.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,3⟩)
  | _,_ => none

def ef : StatePerm := swapStates (4 : Fin 6) 5
def permPartial (p : PartialMachine) : PartialMachine := fun slot =>
  (p (ef.backward slot.1,slot.2)).map (Option.map (renameMove ef))

theorem triple_eq :
    BB6.Agent50Raw34TripleSweep.pE = permPartial tripleF := by
  have h : ∀ (s : Fin 6) (b : Bool),
      BB6.Agent50Raw34TripleSweep.pE (s,b) =
        permPartial tripleF (s,b) := by
    decide
  funext slot
  rcases slot with ⟨s,b⟩
  exact h s b

theorem alternating_eq :
    BB6.Agent50Raw34Alternating.p = permPartial alternatingF := by
  have h : ∀ (s : Fin 6) (b : Bool),
      BB6.Agent50Raw34Alternating.p (s,b) =
        permPartial alternatingF (s,b) := by
    decide
  funext slot
  rcases slot with ⟨s,b⟩
  exact h s b

theorem compatible_perm (p : PartialMachine) (m : Machine)
    (hm : compatible p m) :
    compatible (permPartial p) (renameTable ef m) := by
  intro slot target hp
  unfold permPartial at hp
  cases hs : p (ef.backward slot.1,slot.2) with
  | none => simp [hs] at hp
  | some v =>
    have hm' := hm (ef.backward slot.1,slot.2) v hs
    simpa [renameTable,hs,hm'] using hp

theorem transport_never (p source : PartialMachine)
    (eq : source = permPartial p)
    (hn : ∀ m : Machine, compatible source m → NeverHalts m)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  intro n
  have hz : ef.forward 0 = 0 := by decide
  have hb : renameConfig ef blank = blank := by
    simp [renameConfig,blank,hz]
  have hr := rename_run ef m blank n
  rw [hb] at hr
  have hc : compatible source (renameTable ef m) := by
    rw [eq]
    exact compatible_perm p m hm
  have hLive := hn (renameTable ef m) hc n
  rw [hr] at hLive
  cases hRun : run m n blank with
  | none => simp [hRun] at hLive
  | some cfg => rfl

theorem tripleF_never (m : Machine) (hm : compatible tripleF m) :
    NeverHalts m :=
  transport_never tripleF BB6.Agent50Raw34TripleSweep.pE triple_eq
    BB6.Agent50Raw34TripleSweep.E_never m hm

theorem alternatingF_never (m : Machine) (hm : compatible alternatingF m) :
    NeverHalts m :=
  transport_never alternatingF BB6.Agent50Raw34Alternating.p alternating_eq
    BB6.Agent50Raw34Alternating.never m hm

#print axioms triple_eq
#print axioms alternating_eq
#print axioms compatible_perm
#print axioms transport_never
#print axioms tripleF_never
#print axioms alternatingF_never
end BB6.Agent40Raw34ConjugateGrowth
