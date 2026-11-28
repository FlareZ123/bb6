import Box33D17V12IEntry
import Box33D17V12ICarry
import Box33D17V12IRules

namespace MacroI
set_option maxRecDepth 30000
set_option maxHeartbeats 0

/-- Joint exact stream-model certificate: original blank entry and three
    unbounded packet laws, each uniform in the entire remaining tape tail.
    The independent source bridge to BB6Coverage is a separate obligation. -/
theorem blank_and_three_packets :
  (run 490 (cfg .A z z) =
    some (phase 3 (word (bits "1010111") z))) ∧
  (∀ (j : Nat) (r : Stream),
    run (108+32*j) (phase j (word (bits "11000") r)) =
    some (phase (j+1) (word (bits "10101") r))) ∧
  (∀ (j : Nat) (r : Stream),
    run (110+32*j) (phase j (word (bits "10101000") r)) =
    some (phase (j+1) (word (bits "11000001") r))) ∧
  (∀ (j : Nat) (r : Stream),
    run (132+32*j) (phase j (word (bits "1010100101000") r)) =
    some (phase (j+1) (word (bits "1100000000101") r))) := by
  exact ⟨blank_entry, oddPacket, evenPacket, carryPacket⟩

#print axioms blank_and_three_packets
end MacroI
