import Raw10HardRootR1Adapter
import Box17SourceFull

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Raw10R1SourceAdapter

open BB6Coverage

/-- The hard-root adapter and Agent13's source-adapted r1 table are the same
literal six-state machine, slot for slot. -/
theorem r1_eq_box17 :
    BB6.Agent50Raw10HardRootR1Adapter.r1 = BB6.Agent13.Box17.r1Machine := by
  funext s
  rcases s with ⟨q,b⟩
  fin_cases q <;> cases b <;> rfl

/-- The pinned original Cryptids nonhalting theorem supplies the premise
required by Agent50's one-hole hard-root adapter. -/
theorem r1_never :
    NeverHalts BB6.Agent50Raw10HardRootR1Adapter.r1 := by
  rw [r1_eq_box17]
  exact BB6.Agent13.Box17.r1_source_never

/-- Unconditional source-level r1 discharge of the raw10 hard-root adapter.
The remaining non-r1 residual rectangles and held leaf remain explicit
premises; this theorem does not claim the whole B0=1LC parent is closed. -/
theorem raw10CoverWithR1Source (B : Nat) (hB : 7014 ≤ B)
    (hHeld : ∀ m, compatible BB6.Agent49BoxBridge.held m →
      WeightedBound B m)
    (hOpen : ∀ r ∈ BB6.Agent17Raw10CombinedConsumer.raw10RemainderWithCycleAndHalt,
      ∀ m, Fits r m →
        (r = BB6.Agent50Raw10HardRootR1Adapter.r1Box24 →
          ¬ compatible BB6.Agent50Raw10HardRootR1Adapter.r1Leaf m) →
        WeightedBound B m) :
    Cover (WeightedBound B) BB6.Agent49BoxBridge.firstOneB0_1LC :=
  BB6.Agent50Raw10HardRootR1Adapter.raw10CoverWithR1
    B hB hHeld r1_never hOpen

#print axioms r1_eq_box17
#print axioms r1_never
#print axioms raw10CoverWithR1Source

end BB6.Agent17Raw10R1SourceAdapter
