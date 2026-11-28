import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
E/F-state conjugates of the four late-entry genuine Raw34 sidecycles.
The physical tables are independently checked on the original source
finite-tape semantics, without relying on the source F proof. E1/E0
are assigned according to the F1/F0 conjugation; F0/F1 remain
unassigned even if HALT. Proof checker checks every tape cell on the
retained left half-line for each authentic recurrence.
-/
namespace BB6.Agent40Raw34ELongSideCycles
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle

structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int

def witnesses : List CycleWitness := [
  ⟨[21,0,22,0,11,3,16,12,18,4,0,0],72,1,false,6⟩,
  ⟨[21,0,22,0,11,23,16,12,18,4,0,0],64,1,false,6⟩,
  ⟨[21,0,22,0,11,10,16,12,17,18,0,0],60,5,false,10⟩,
  ⟨[21,0,22,0,11,6,16,12,23,11,0,0],60,3,false,11⟩
]

def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary

theorem count : witnesses.length = 4 := by decide
theorem checked : witnesses.all checkCycle = true := by decide +kernel

theorem all_never (w : CycleWitness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    NeverHalts m := by
  have hh : checkCycle w = true := List.all_eq_true.mp checked w hw
  obtain ⟨hp,hcheck⟩ :
      decide (0 < w.period) = true ∧
      fastSideCycleCheck (table w.codes)
        w.entry w.period w.right w.boundary = true := by
    simpa only [checkCycle, Bool.and_eq_true] using hh
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary
    (of_decide_eq_true hp) hcheck m hm

#print axioms count
#print axioms checked
#print axioms all_never
end BB6.Agent40Raw34ELongSideCycles
