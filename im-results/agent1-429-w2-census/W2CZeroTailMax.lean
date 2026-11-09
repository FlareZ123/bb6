import W4HeadMax
import W4JuncOne
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2CZeroTailMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4JuncOne

/-- The six primitive steps after a prepared C/0 gateway backtrack two
    cells to E/1, visiting at most one new rightmost cell. This is
    uniform in the unbounded one-block length. -/
theorem c0_to_e1_max (v : Nat) :
    runWithMax 6 (z 2 (true::false::ones (2*v+14)) false []) =
      some (z 4 (ones (2*v+14)) true [true,false,true], -2, 1) := by
  rfl

/-- Every primitive prefix of an E/1 sweep over an arbitrary one-block
    stays at or to the left of its initial head coordinate. -/
theorem e1_sweep_max (n : Nat) (tail suffix : List Bool) :
    runWithMax n (z 4 (ones n ++ tail) true suffix) =
      some (z 4 tail true (ones n ++ suffix), -((n : Nat) : Int), 0) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      have hstep : runWithMax 1 (z 4 (ones (n+1) ++ tail) true suffix) =
          some (z 4 (ones n ++ tail) true (true::suffix), -1, 0) := by
        rfl
      rw [show n+1 = 1+n by omega, runWithMax_add,
          show 1+n = n+1 by omega, hstep]
      simp only [Option.bind_some]
      rw [ih (true::suffix)]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · have hright : ones n ++ (true::suffix) =
            ones (n+1) ++ suffix := by
          simp [ones, List.replicate_succ',List.append_assoc]
        rw [hright]
      · constructor <;> omega

/-- The fixed twelve-step E/1 finishing suffix moves right four positions
    in total and attains no greater position. The untouched suffix is
    arbitrary. -/
theorem e1_tail12_max (suffix : List Bool) :
    runWithMax 12 (z 4 [] true (ones 4 ++ suffix)) =
      some (z 0 (ones 6) true suffix, 4, 4) := by
  rfl

/-- Uniform all-prefix maximum for the ENTIRE return following the
    unique C/0 gate of a prepared Junc(2,v,1).
    The gate's next primitive step reaches exactly one cell farther right;
    no subsequent instruction exceeds that position. -/
theorem c0_tail_max (v : Nat) :
    runWithMax (2*v+32) (z 2 (true::false::ones (2*v+14)) false []) =
      some (junc 0 0 (2*v+10), -(((2*v+12 : Nat) : Int)), 1) := by
  have h6 := c0_to_e1_max v
  have hE := e1_sweep_max (2*v+14) [] [true,false,true]
  simp only [List.append_nil] at hE
  have h12 := e1_tail12_max (ones (2*v+10) ++ [true,false,true])
  have hones : ones (2*v+14) = ones 4 ++ ones (2*v+10) := by
    change List.replicate (2*v+14) true =
      List.replicate 4 true ++ List.replicate (2*v+10) true
    rw [show 2*v+14 = 4+(2*v+10) by omega, ← List.replicate_append_replicate]
  have hlist : ones (2*v+14) ++ [true,false,true] =
      ones 4 ++ (ones (2*v+10) ++ [true,false,true]) := by
    rw [hones,List.append_assoc]
  rw [show 2*v+32 = 6+((2*v+14)+12) by omega, runWithMax_add,h6]
  simp only [Option.bind_some]
  rw [runWithMax_add,hE]
  simp only [Option.bind_some]
  rw [hlist,h12]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · change z 0 (ones 6) true (ones (2*v+10) ++ [true,false,true]) =
        z 0 (true :: ones 5) true (true :: (ones (2*v+10) ++ [false,true]))
    rw [ones_right_101]
    rfl
  · constructor <;> simp [Int.max_def] <;> omega

#print axioms c0_to_e1_max
#print axioms e1_sweep_max
#print axioms e1_tail12_max
#print axioms c0_tail_max

end BB429W2CZeroTailMax
