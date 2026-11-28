import Raw34D1RDOneStepCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent23Raw34D1RDOneStepPilot
open BB6Coverage BB6.Agent23Raw34Next

/-! New D1=1RD, C1∈{0LF,0RF,1LF,1RF} one-more-hole
nonhalting/halting cylinders. Witnesses are checked directly against
the source partial-machine transition and tape semantics. -/
def witnesses : List Witness := [
  ⟨[21,0,22,0,11,7,16,23,0,0,1,0], .halt 8⟩,
  ⟨[21,0,22,0,11,7,16,23,0,0,10,0], .side 4 5 true (2)⟩,
  ⟨[21,0,22,0,11,7,16,23,0,0,22,0], .side 4 5 true (2)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,1], .halt 8⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,2], .side 0 9 true (0)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,3], .side 1 8 true (1)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,4], .side 2 7 true (2)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,5], .side 3 6 true (2)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,8], .side 0 9 true (0)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,9], .side 1 8 true (1)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,10], .side 2 7 true (2)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,11], .side 3 6 true (2)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,16], .side 4 5 true (2)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,20], .side 0 9 true (0)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,21], .side 1 8 true (1)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,22], .side 2 7 true (2)⟩,
  ⟨[21,0,22,0,11,13,16,23,0,0,0,23], .side 6 3 true (3)⟩,
  ⟨[21,0,22,0,11,19,16,23,0,0,1,0], .halt 8⟩,
  ⟨[21,0,22,0,11,19,16,23,0,0,10,0], .side 7 2 true (2)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,1], .halt 8⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,5], .side 5 4 true (3)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,8], .side 0 9 true (0)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,9], .side 1 8 true (1)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,10], .side 2 7 true (2)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,11], .side 3 6 true (2)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,16], .side 7 2 true (3)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,17], .side 5 5 true (3)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,20], .side 0 9 true (0)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,21], .side 1 8 true (1)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,22], .side 2 7 true (2)⟩,
  ⟨[21,0,22,0,11,25,16,23,0,0,0,23], .side 6 3 true (3)⟩
]

theorem count : witnesses.length = 31 := by decide
theorem checked : witnesses.all check = true := by decide +kernel
theorem sound (w : Witness) (hw : w ∈ witnesses) :
    ∀ m, compatible (table w.codes) m → WeightedBound 32 m :=
  check_sound w (List.all_eq_true.mp checked w hw)
#print axioms count
#print axioms checked
#print axioms sound
end BB6.Agent23Raw34D1RDOneStepPilot
