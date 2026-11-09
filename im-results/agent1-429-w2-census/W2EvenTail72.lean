import W4HeadMax
import W4JuncOne
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2EvenTail72

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429W4HeadMax

/-- Twelve six-instruction primitive certificates with an arbitrary untouched
    right suffix. The complete 72-step trajectory never inspects this suffix. -/

private def cfg0 (tail : List Bool) : Zipper :=
  z 4 [false,true,false,true,true,true,true,true,true] true ([true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg1 (tail : List Bool) : Zipper :=
  z 4 [true,true,true,true,true] true ([true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg2 (tail : List Bool) : Zipper :=
  z 4 [] false ([true,true,true,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg3 (tail : List Bool) : Zipper :=
  z 5 [false,true,true] true ([false,true,true,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg4 (tail : List Bool) : Zipper :=
  z 5 [true,true,true,true,true] true ([false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg5 (tail : List Bool) : Zipper :=
  z 5 [] false ([false,true,false,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg6 (tail : List Bool) : Zipper :=
  z 2 [true,true] true ([true,true,false,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg7 (tail : List Bool) : Zipper :=
  z 0 [true,true,true,true] false ([false,true,false,true,false,true,true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg8 (tail : List Bool) : Zipper :=
  z 2 [true,false,true,false,true,true,true,true,true,true] true ([true,true,false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg9 (tail : List Bool) : Zipper :=
  z 0 [true,true,true,false,true,false,true,true,true,true,true,true] false ([false,true,true,true,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg10 (tail : List Bool) : Zipper :=
  z 0 [true,true,true,true,true,false,true,false,true,true,true,true,true,true] false ([true,false,true,true,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg11 (tail : List Bool) : Zipper :=
  z 0 [true,true,true,true,true,true,true,false,true,false,true,true,true,true,true,true] true ([true,false,true,true,true,true,true,true,true,true,true,true] ++ tail)

private def cfg12 (tail : List Bool) : Zipper :=
  z 0 [true,false,true,false,true,true,true,true,true,true] true ([true,false,true,false,true,false,true,false,true,true,true,true,true,true,true,true,true,true] ++ tail)

private theorem segment0 (tail : List Bool) :
    runWithMax 6 (cfg0 tail) = some (cfg1 tail, -4, 0) := by rfl

private theorem segment1 (tail : List Bool) :
    runWithMax 6 (cfg1 tail) = some (cfg2 tail, -6, 0) := by rfl

private theorem segment2 (tail : List Bool) :
    runWithMax 6 (cfg2 tail) = some (cfg3 tail, 2, 3) := by rfl

private theorem segment3 (tail : List Bool) :
    runWithMax 6 (cfg3 tail) = some (cfg4 tail, 2, 3) := by rfl

private theorem segment4 (tail : List Bool) :
    runWithMax 6 (cfg4 tail) = some (cfg5 tail, -6, 0) := by rfl

private theorem segment5 (tail : List Bool) :
    runWithMax 6 (cfg5 tail) = some (cfg6 tail, 0, 1) := by rfl

private theorem segment6 (tail : List Bool) :
    runWithMax 6 (cfg6 tail) = some (cfg7 tail, 2, 2) := by rfl

private theorem segment7 (tail : List Bool) :
    runWithMax 6 (cfg7 tail) = some (cfg8 tail, 6, 6) := by rfl

private theorem segment8 (tail : List Bool) :
    runWithMax 6 (cfg8 tail) = some (cfg9 tail, 2, 2) := by rfl

private theorem segment9 (tail : List Bool) :
    runWithMax 6 (cfg9 tail) = some (cfg10 tail, 2, 4) := by rfl

private theorem segment10 (tail : List Bool) :
    runWithMax 6 (cfg10 tail) = some (cfg11 tail, 2, 4) := by rfl

private theorem segment11 (tail : List Bool) :
    runWithMax 6 (cfg11 tail) = some (cfg12 tail, -6, 0) := by rfl

/-- Unbounded right context remains arbitrary throughout all 72 steps.
    The sharp head maximum over this entire phase is four cells right. -/
theorem all72 (tail : List Bool) :
    runWithMax 72 (cfg0 tail) = some (cfg12 tail,-4,4) := by
  rw [show (72:Nat) = 6 + (6 + (6 + (6 + (6 + (6 + (6 + (6 + (6 + (6 + (6 + (6))))))))))) by omega]

  rw [runWithMax_add,segment0]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment1]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment2]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment3]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment4]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment5]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment6]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment7]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment8]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment9]
  simp only [Option.bind_some]

  rw [runWithMax_add,segment10]
  simp only [Option.bind_some]

  rw [segment11]

  rfl

/-- Sharp all-prefix head maximum for the fixed even E/1 return tail,
    parameter uniform in the arbitrarily long preserved right one-block. -/
theorem even_E1_tail72_max (k : Nat) :
  runWithMax 72
    (z 4 (pairs01 2 ++ ones 5) true (ones (4*k+13) ++ [true,false,true])) =
  some (junc 2 4 (4*k+9), -4, 4) := by
  have hword : ones (4*k+13) ++ [true,false,true] =
      ones 14 ++ (ones (4*k) ++ [false,true]) := by
    rw [show 4*k+13=13+4*k by omega]
    simp only [ones]
    rw [← List.replicate_append_replicate (n:=13) (m:=4*k) (a:=true)]
    simpa [ones,List.append_assoc] using (BB429W4JuncOne.ones_right_101 (4*k))
  have hstart :
      z 4 (pairs01 2 ++ ones 5) true
        (ones (4*k+13) ++ [true,false,true]) =
      cfg0 (ones (4*k) ++ [false,true]) := by
    rw [hword]
    rfl
  have hend : cfg12 (ones (4*k) ++ [false,true]) =
      junc 2 4 (4*k+9) := by
    simp only [cfg12,junc]
    have hones : ones (4*k+9) = ones 9 ++ ones (4*k) := by
      change List.replicate (4*k+9) true =
        List.replicate 9 true ++ List.replicate (4*k) true
      rw [show 4*k+9=9+4*k by omega, ← List.replicate_append_replicate]
    rw [hones]
    rfl
  rw [hstart,all72,hend]

#print axioms all72
#print axioms even_E1_tail72_max

end BB429W2EvenTail72
