import BB429GateArithmetic25

namespace BB429GateArithmetic24

/-- Agent1's exact 25 candidates intersected with Agent6's separately
    source-certified exclusion of the 81(mod512) cylinder. -/
def candidate (a : Nat) : Bool :=
  BB429GateArithmetic25.candidate a && (a%512 != 81)

def survivors : List Nat := (List.range 2048).filter candidate

set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem survivors_exact :
    survivors = [9,73,117,201,209,245,337,465,565,637,765,849,
      949,1021,1033,1097,1141,1233,1361,1673,1789,1917,1973,2045] := by
  decide

theorem survivors_cardinality : survivors.length = 24 := by
  rw [survivors_exact]
  decide

#print axioms survivors_exact
#print axioms survivors_cardinality
end BB429GateArithmetic24
