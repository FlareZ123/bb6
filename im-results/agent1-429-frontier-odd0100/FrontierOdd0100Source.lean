import CZeroEvenReturn
import Lean.Elab.Tactic.Omega

namespace BB429Odd0100Source
open BB429OddExcursion BB429CZeroEvenReturn

private theorem shift_one (m : Nat) (tail : List Bool) :
    (List.replicate (2*m) true) ++ true :: tail =
    true :: (List.replicate (2*m) true) ++ tail := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hrep : List.replicate (2*(m+1)) true =
      true :: true :: List.replicate (2*m) true := by
      rw [show 2*(m+1)=2*m+2 by omega]
      simp [List.replicate_succ]
    rw [hrep]
    simpa only [List.cons_append] using congrArg (fun xs => true :: true :: xs) ih

private theorem c3 (m : Nat) (tail : List Bool) :
  run 3 (z 2 (true :: List.replicate (2*m) true ++
    [false,true,false,false] ++ tail) false []) =
  some (z 0 (List.replicate (2*m) true ++
    [false,true,false,false] ++ tail) true [false,true]) := by rfl

private theorem turn14 (tail r : List Bool) :
  run 14 (z 0 ([false,true,false,false] ++ tail) true r) =
  some (z 0 ([true,true,true,true] ++ tail) false r) := by rfl

private theorem finish4 (l : List Bool) :
  run 4 (z 0 l false [false,true]) =
  some (z 2 ([true,false,true,true] ++ l) false []) := by rfl

/-- An exact original-source zipper return, for every m and every remote left
    suffix. After 4m+21 primitive instructions C/0 returns with right blank. -/
theorem odd_0100_original (m : Nat) (tail : List Bool) :
  run (4*m+21)
    (z 2 (List.replicate (2*m) true ++ [true,false,true,false,false] ++ tail) false []) =
  some (z 2 ([true,false] ++ List.replicate (2*m+6) true ++ tail) false []) := by
  have hstart : List.replicate (2*m) true ++ [true,false,true,false,false] ++ tail =
      true :: List.replicate (2*m) true ++ [false,true,false,false] ++ tail := by
    simpa only [List.append_assoc, List.cons_append] using shift_one m ([false,true,false,false] ++ tail)
  rw [show 4*m+21=3+(2*m+(14+(2*m+4))) by omega,run_add,hstart,c3]
  simp only [Option.bind_some]
  rw [run_add]
  rw [show List.replicate (2*m) true ++ [false,true,false,false] ++ tail =
      List.replicate (2*m) true ++ ([false,true,false,false] ++ tail) by simp [List.append_assoc]]
  rw [af_pairs]
  simp only [Option.bind_some]
  rw [run_add,turn14]
  simp only [Option.bind_some]
  rw [run_add,a_right_pairs_exact]
  simp only [Option.bind_some]
  rw [finish4]
  simp only [Option.some.injEq]
  congr 1
  have hfront : ([true,true] ++ List.replicate (2*m) true ++ [true,true,true,true]) =
      List.replicate (2*m+6) true := by
    change List.replicate 2 true ++ List.replicate (2*m) true ++
      List.replicate 4 true = List.replicate (2*m+6) true
    rw [List.append_assoc, List.replicate_append_replicate,
      List.replicate_append_replicate]
    congr 1
    omega
  simpa [List.append_assoc] using congrArg (fun v : List Bool => v ++ tail) hfront

#print axioms odd_0100_original
end BB429Odd0100Source
