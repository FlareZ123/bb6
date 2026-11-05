import BB429GateArithmetic
namespace BB429GateArithmetic25

/-- Result of adding Agent1's fifteen further proven whole-root
    residue exclusions to the exact earlier 40-class filter. -/
def candidate (a : Nat) : Bool :=
  BB429GateArithmetic.candidate a &&
  (a%2048 != 53) &&
  (a%2048 != 585) &&
  (a%2048 != 629) &&
  (a%2048 != 649) &&
  (a%2048 != 721) &&
  (a%2048 != 1225) &&
  (a%2048 != 1269) &&
  (a%2048 != 1461) &&
  (a%2048 != 1489) &&
  (a%2048 != 1589) &&
  (a%2048 != 1717) &&
  (a%2048 != 1737) &&
  (a%2048 != 1781) &&
  (a%2048 != 1873) &&
  (a%2048 != 2001)

def survivors : List Nat := (List.range 2048).filter candidate

set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

theorem survivors_exact :
    survivors = [9, 73, 81, 117, 201, 209, 245, 337, 465, 565, 637, 765, 849, 949, 1021, 1033, 1097, 1141, 1233, 1361, 1673, 1789, 1917, 1973, 2045] := by
  decide

theorem survivors_cardinality : survivors.length = 25 := by
  rw [survivors_exact]
  decide

#print axioms survivors_exact
#print axioms survivors_cardinality
end BB429GateArithmetic25
