import W4HeadMax
import BB429JuncHeadExcursion
import Lean.Elab.Tactic.Omega

namespace BB429W4JuncMax

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion BB429W4HeadMax

/-- During the entire first twenty-step preparation of a zero-left Junc,
    the head never visits a position to the right of its input head. -/
theorem junc0_prep20_max (v w : Nat) :
    runWithMax 20 (junc 0 v w) =
      some (z 1 (ones 5) false
        (true :: (pairs01 (v+2) ++ ones w ++ [false,true])), -4, 0) := by
  rfl

private theorem pairs01_rightstep (n : Nat) :
    pairs01 (n+1) = pairs01 n ++ [false,true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false::true::pairs01 (n+1) = (false::true::pairs01 n) ++ [false,true]
      rw [ih]
      rfl

/-- Every B/0, C/1 pair moves right exactly twice, with the final position
    equal to the greatest head coordinate on that pair. -/
theorem shift_B01_pair_max (left suffix : List Bool) :
    runWithMax 2 (z 1 left false (true::true::suffix)) =
      some (z 1 (false::true::left) true suffix, 2, 2) := by rfl

/-- A block of arbitrarily many B/0,C/1 pairs travels monotonically right.
    Its all-prefix max is exactly its final displacement. -/
theorem shift_B01_max (v : Nat) (left suffix : List Bool) :
    runWithMax (2*(v+1))
      (z 1 left false (true :: (pairs01 v ++ (true :: suffix)))) =
      some (z 1 (pairs01 (v+1) ++ left) true suffix,
        ((2*(v+1) : Nat) : Int), ((2*(v+1) : Nat) : Int)) := by
  induction v generalizing left suffix with
  | zero =>
      simpa [pairs01] using (shift_B01_pair_max left suffix)
  | succ v ih =>
      have hpair :
          runWithMax 2
            (z 1 left false (true :: (pairs01 (v+1) ++ (true :: suffix)))) =
          some (z 1 (false :: true :: left) false
            (true :: (pairs01 v ++ (true :: suffix))), 2, 2) := by
        rfl
      rw [show 2*(v+2) = 2 + 2*(v+1) by omega, runWithMax_add, hpair]
      simp only [Option.bind_some]
      rw [ih (false::true::left) suffix]
      simp only [Option.map_some]
      have hleft : pairs01 (v+1) ++ (false :: true :: left) =
          pairs01 (v+2) ++ left := by
        calc
          pairs01 (v+1) ++ (false :: true :: left) =
            pairs01 (v+1) ++ ([false,true] ++ left) := rfl
          _ = (pairs01 (v+1) ++ [false,true]) ++ left := by rw [← List.append_assoc]
          _ = pairs01 (v+2) ++ left := by
            exact congrArg (fun ys : List Bool => ys ++ left)
              (pairs01_rightstep (v+1)).symm
      rw [hleft]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · trivial
      · constructor <;> omega

/-- The final five steps from B/1 to C/0 are strictly rightward, and
    the entire right stack has become blank by the C/0 endpoint. -/
theorem b1_to_czero5_max (left : List Bool) :
    runWithMax 5 (z 1 left true [false,true]) =
      some (z 2 (ones 5 ++ left) false [], 5, 5) := by rfl

/-- For every Junc(0,v,1), its first C/0 visit is a **new right-head
    record**: among all primitive steps up to and including this event,
    no position exceeds 2v+7, which is exactly the event's head coordinate.
    Its entire right tape is blank. -/
theorem junc0_w1_first_czero_max (v : Nat) :
    runWithMax (2*v+31) (junc 0 v 1) =
      some (z 2 (ones 5 ++ (pairs01 (v+3) ++ ones 5)) false [],
        ((2*v+7 : Nat) : Int), ((2*v+7 : Nat) : Int)) := by
  have hprep := junc0_prep20_max v 1
  have hshift := shift_B01_max (v+2) (ones 5) [false,true]
  have htail := b1_to_czero5_max (pairs01 (v+3) ++ ones 5)
  have hinput : z 1 (ones 5) false
      (true :: (pairs01 (v+2) ++ ones 1 ++ [false,true])) =
     z 1 (ones 5) false (true :: (pairs01 (v+2) ++ (true :: [false,true]))) := by
    simp [ones, List.append_assoc]
  have htime : 2*v+31 = 20 + (2*((v+2)+1)+5) := by omega
  rw [htime, runWithMax_add, hprep]
  simp only [Option.bind_some]
  rw [hinput, runWithMax_add, hshift]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

#print axioms junc0_prep20_max
#print axioms shift_B01_max
#print axioms junc0_w1_first_czero_max

end BB429W4JuncMax
