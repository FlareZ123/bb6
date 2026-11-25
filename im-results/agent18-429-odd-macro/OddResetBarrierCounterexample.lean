import Q0DoubleBarrier

namespace BB429Q0Macro.RankBarrier
open BB429Q0Macro
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

private def B : Nat := 23*16^117
private def w : List Digit := List.replicate 115 .zero ++ [.five,.zero]
private def v : List Digit := List.replicate 115 .zero ++ [.five,.five]
private def z : List Digit := List.replicate 115 .five ++ [.zero,.zero]
private def p : Nat := B-354
private def y : Nat := 13*16^115
private def Y : Nat := 115*16^115
private def P2 : Nat := B+357
private def Y2 : Nat := (P2-B/256)/3
private def P3 : Nat := B+1053
private def Y3 : Nat := (B+1024)/768

/-- A strict-interior crossing at coefficient 23, scale 117, overshoot 0.
    Refutes the all-scale two-row-barrier conjecture. -/
theorem cross2_23_0_117 : Cross2 23 0 117 := by
  refine ⟨w,v,z,p,y,Y,P2,Y2,P3,Y3,by decide,by decide,by decide,by decide,by decide,?_,?_,?_⟩
  · apply trace_of_formula
    · decide
    · decide
  · apply trace_of_formula
    · decide
    · decide
  · apply trace_of_formula
    · decide
    · decide

theorem barrier_23_117_false : barrier 23 117 = false := by
  cases h : barrier 23 117 with
  | false => rfl
  | true => exact False.elim (barrier_sound h (b:=0) (by decide) cross2_23_0_117)

#print axioms cross2_23_0_117
#print axioms barrier_23_117_false
end BB429Q0Macro.RankBarrier
