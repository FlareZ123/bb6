import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Thirty-four genuine all-time nonhalting first-new-query F cycles.  Fix only
D1 (the 1-read instruction of D) and F0 (the first F-blank instruction);
all other six previously undefined instructions are fully arbitrary.
Each side-cycle witness is checked on the real blank tape against the
original finiteWindow/finiteTailEq checker, not inferred by simulation.
Unlike closed-state graph certificates this allows arbitrary HALTs in
unused instructions.
-/
namespace BB6.Agent40Raw34FDepth2Cycles
open BB6Coverage BB6.Agent23Raw34Next BB6Coverage.Agent50SideCycle
structure CycleWitness where
  codes : List Nat
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int

def witnesses : List CycleWitness := [
  ⟨[21,0,22,0,11,0,16,7,0,0,8,0], 0, 7, true, 0⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,9,0], 1, 6, true, 1⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,10,0], 2, 5, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,11,0], 3, 4, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,13,0], 6, 1, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,20,0], 0, 7, true, 0⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,21,0], 1, 6, true, 1⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,22,0], 2, 5, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,7,0,0,25,0], 6, 1, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,19,0,0,11,0], 5, 2, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,2,0], 0, 7, true, 0⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,3,0], 1, 6, true, 1⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,4,0], 2, 5, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,5,0], 3, 4, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,8,0], 0, 7, true, 0⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,9,0], 1, 6, true, 1⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,10,0], 2, 5, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,11,0], 3, 4, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,13,0], 6, 1, true, 4⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,16,0], 4, 3, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,20,0], 0, 7, true, 0⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,21,0], 1, 6, true, 1⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,22,0], 2, 5, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,13,0,0,25,0], 6, 1, true, 4⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,5,0], 5, 2, true, 3⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,8,0], 0, 7, true, 0⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,9,0], 1, 6, true, 1⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,10,0], 2, 5, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,11,0], 3, 4, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,13,0], 6, 1, true, 4⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,20,0], 0, 7, true, 0⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,21,0], 1, 6, true, 1⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,22,0], 2, 5, true, 2⟩,
  ⟨[21,0,22,0,11,0,16,25,0,0,25,0], 6, 1, true, 4⟩
]
def checkCycle (w : CycleWitness) : Bool :=
  decide (0 < w.period) &&
    fastSideCycleCheck (table w.codes) w.entry w.period w.right w.boundary

theorem count : witnesses.length = 34 := by decide
theorem checked : witnesses.all checkCycle = true := by decide +kernel

theorem all_never (w : CycleWitness) (hw : w ∈ witnesses)
    (m : Machine) (hm : compatible (table w.codes) m) :
    NeverHalts m := by
  have hh : checkCycle w = true := List.all_eq_true.mp checked w hw
  obtain ⟨hp,hcheck⟩ : decide (0 < w.period) = true ∧
      fastSideCycleCheck (table w.codes)
        w.entry w.period w.right w.boundary = true := by
    simpa only [checkCycle, Bool.and_eq_true] using hh
  exact fastSideCycleCheck_sound (table w.codes)
    w.entry w.period w.right w.boundary
    (of_decide_eq_true hp) hcheck m hm

#print axioms count
#print axioms checked
#print axioms all_never
end BB6.Agent40Raw34FDepth2Cycles
