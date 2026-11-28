import Raw34BinaryLeftOdometer
import Raw34UnaryLeftGrowth
import WeightedTNF

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent40Raw34LeftOdometerConjugateE
open BB6Coverage BB6.Agent13BlankDelay

/-!
Original-source E/F state conjugacy transports *unbounded* Raw34
left-binary and left-unary growth, without mirroring the tape.
This proves E0=0LB, D1=0LE variants of the 0RC binary odometer,
and both D1=0LE and D1=1LE variants of the 1RC unary growth.
The three additional E-branch cylinders are disjoint from the F
sources because their D1 physical transitions differ.
Until original-source Lean CI passes, these are proof candidates.
-/

def pE (c1 w : Bool) : PartialMachine := fun s =>
  match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,1⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨c1,true,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨w,false,4⟩)
  | 4,false => some (some ⟨false,false,1⟩)
  | _,_ => none

def ef : StatePerm := swapStates (4 : Fin 6) 5

def permPartial (p : PartialMachine) : PartialMachine := fun slot =>
  (p (ef.backward slot.1,slot.2)).map (Option.map (renameMove ef))

theorem binary_source_eq :
    BB6.Agent40Raw34BinaryLeftOdometer.p = permPartial (pE false false) := by
  have h : ∀ (s : Fin 6) (b : Bool),
      BB6.Agent40Raw34BinaryLeftOdometer.p (s,b) =
      permPartial (pE false false) (s,b) := by decide
  funext slot
  rcases slot with ⟨s,b⟩
  exact h s b

theorem unary_source_eq (w : Bool) :
    BB6.Agent40Raw34UnaryLeftGrowth.p w = permPartial (pE true w) := by
  have h : ∀ (s : Fin 6) (b : Bool),
      BB6.Agent40Raw34UnaryLeftGrowth.p w (s,b) =
      permPartial (pE true w) (s,b) := by
    cases w <;> decide
  funext slot
  rcases slot with ⟨s,b⟩
  exact h s b

theorem perm_compatible (p : PartialMachine) (m : Machine)
    (hm : compatible p m) :
    compatible (permPartial p) (renameTable ef m) := by
  intro slot target hp
  unfold permPartial at hp
  cases hs : p (ef.backward slot.1,slot.2) with
  | none => simp [hs] at hp
  | some v =>
    have hm' := hm (ef.backward slot.1,slot.2) v hs
    simpa [renameTable,hs,hm'] using hp

theorem lift_never (p q : PartialMachine)
    (heq : p = permPartial q)
    (hnever : ∀ m, compatible p m → NeverHalts m)
    (m : Machine) (hm : compatible q m) : NeverHalts m := by
  intro n
  have hz : ef.forward 0 = 0 := by decide
  have hb : renameConfig ef blank = blank := by
    simp [renameConfig,blank,hz]
  have hr := rename_run ef m blank n
  rw [hb] at hr
  have hc : compatible p (renameTable ef m) := by
    rw [heq]
    exact perm_compatible q m hm
  have hLive := hnever (renameTable ef m) hc n
  rw [hr] at hLive
  cases h : run m n blank with
  | none => simp [h] at hLive
  | some c => rfl

/-- Genuine blank-start, original-source nonhalting for E0=0LB and
    C1=0RC, D1=0LE. Arbitrary A1,E1,F0,F1. -/
theorem binary_E_never (m : Machine)
    (hm : compatible (pE false false) m) : NeverHalts m :=
  lift_never BB6.Agent40Raw34BinaryLeftOdometer.p (pE false false)
    binary_source_eq BB6.Agent40Raw34BinaryLeftOdometer.all_time_never m hm

/-- Both E-branch write-bit unary cylinders, all free cells arbitrary. -/
theorem unary_E_never (w : Bool) (m : Machine)
    (hm : compatible (pE true w) m) : NeverHalts m :=
  lift_never (BB6.Agent40Raw34UnaryLeftGrowth.p w) (pE true w)
    (unary_source_eq w)
    (BB6.Agent40Raw34UnaryLeftGrowth.all_time_never w) m hm

#print axioms binary_source_eq
#print axioms unary_source_eq
#print axioms perm_compatible
#print axioms lift_never
#print axioms binary_E_never
#print axioms unary_E_never
end BB6.Agent40Raw34LeftOdometerConjugateE
