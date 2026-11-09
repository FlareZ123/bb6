import W4JuncMax
import W4HeadPrefix
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429ZeroRegularHeadMax

open BB429OddExcursion BB429SourceE1Return
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429W4HeadMax BB429W4JuncMax BB429W4HeadPrefix

/-- Exact maximum through the rightward B/0,C/1 sweep of every regular
zero-left Junc with at least three right marks. -/
theorem junc0_regular_to_b1_max (v w : Nat) :
  runWithMax (2*v+26) (junc 0 v (w+3)) =
    some (z 1 (pairs01 (v+3) ++ ones 5) true
          (ones (w+2) ++ [false,true]),
      ((2*v+2 : Nat) : Int), ((2*v+2 : Nat) : Int)) := by
  have hprep := junc0_prep20_max v (w+3)
  have hshift := shift_B01_max (v+2) (ones 5) (ones (w+2) ++ [false,true])
  have hones : ones (w+3) = true :: ones (w+2) := by
    change List.replicate (w+3) true = true :: List.replicate (w+2) true
    rw [show w+3 = (w+2)+1 by omega]
    rw [List.replicate_succ]
  have hinput : z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ ones (w+3) ++ [false,true])) =
      z 1 (ones 5) false
        (true :: (pairs01 (v+2) ++ (true :: (ones (w+2) ++ [false,true])))) := by
    rw [hones]
    simp [List.append_assoc, List.cons_append]
  have htime : 2*v+26 = 20 + 2*((v+2)+1) := by omega
  rw [htime, runWithMax_add, hprep]
  simp only [Option.bind_some]
  rw [hinput, hshift]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- The final B/1 move reaches the next Junc one cell to the right. -/
theorem junc0_regular_last_max (v w : Nat) :
  runWithMax 1 (z 1 (pairs01 (v+3) ++ ones 5) true
       (ones (w+2) ++ [false,true])) =
    some (junc (v+3) 0 w,1,1) := by
  have hones : ones (w+2) = true :: true :: ones w := by
    change List.replicate (w+2) true = _
    rw [show w+2 = (w+1)+1 by omega]
    rw [List.replicate_succ]
    rw [List.replicate_succ]
    rfl
  rw [hones]
  rfl

/-- Exact all-prefix head maximum and final displacement, for all zero-left
ordinary Junc returns, rather than merely the source's endpoint equality.
The run reaches no position to the right of its final head (+2v+3). -/
theorem junc0_regular_max (v w : Nat) :
  runWithMax (2*v+27) (junc 0 v (w+3)) =
    some (junc (v+3) 0 w,
      ((2*v+3 : Nat) : Int), ((2*v+3 : Nat) : Int)) := by
  have hB := junc0_regular_to_b1_max v w
  have hlast := junc0_regular_last_max v w
  rw [show 2*v+27 = (2*v+26)+1 by omega, runWithMax_add, hB]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- Every primitive prefix of the regular return stays strictly within
the initial rightmost marked cell, which is offset 2v+w+6. -/
theorem junc0_regular_prefix_before_old_mark (v w t : Nat)
    (ht : t ≤ 2*v+27) (p : Zipper × Int × Int)
    (hp : runWithMax t (junc 0 v (w+3)) = some p) :
    p.2.1 < ((2*v+w+6 : Nat) : Int) := by
  have hsum : t+(2*v+27-t) = 2*v+27 := by omega
  have hfull := junc0_regular_max v w
  rw [← hsum] at hfull
  have hbound := runWithMax_prefix_le t (2*v+27-t)
    (junc 0 v (w+3)) p hp
    (junc (v+3) 0 w,
      ((2*v+3 : Nat) : Int), ((2*v+3 : Nat) : Int)) hfull
  simpa only [Prod.snd] at hbound
  omega

#print axioms junc0_regular_to_b1_max
#print axioms junc0_regular_last_max
#print axioms junc0_regular_max
#print axioms junc0_regular_prefix_before_old_mark

end BB429ZeroRegularHeadMax
