import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Genuine late-entry (60--72 physical steps) translated-half-line certificates
for four four-free-slot Raw34 subcylinders. All candidate actions in unassigned
slots remain arbitrary, including HALT. These were discovered by extending the
first-unknown-query search from 60/30 to 600/300, and MUST pass original-source
Lean validation before being counted as proved.

Every witness uses an oriented LEFT half-line, with a strictly leftward
displacement, and is checked directly against finiteWindow and finiteTailEq.
No 100,000-step bounded trace is used as a nonhalting premise.
-/
namespace BB6.Agent40Raw34FLongSideCycles
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle

structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int

def witnesses : List CycleWitness := [
  ⟨[21,0,22,0,11,3,16,13,0,0,19,4],72,1,false,6⟩,
  ⟨[21,0,22,0,11,23,16,13,0,0,19,4],64,1,false,6⟩,
  ⟨[21,0,22,0,11,10,16,13,0,0,17,19],60,5,false,10⟩,
  ⟨[21,0,22,0,11,7,16,13,0,0,23,11],60,3,false,11⟩
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
end BB6.Agent40Raw34FLongSideCycles
