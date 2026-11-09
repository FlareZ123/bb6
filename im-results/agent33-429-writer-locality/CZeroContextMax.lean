import CZeroContext
import W4HeadMax
import Lean.Elab.Tactic.Omega

namespace BB429CZeroContextMax
open BB429OddExcursion BB429SourceE1Delta BB429W4HeadMax

private def ones (n : Nat) : List Bool := List.replicate n true

/-- First six physical moves make precisely one excursion to head+1,
    and end at head-2 with a uniform E/1 stack. -/
private theorem first_max (n : Nat) (left right : List Bool) :
    runWithMax 6
      (z 2 (true::false::(ones n ++ (false::false::left)))
         false (false::right)) =
    some (z 4 (ones n ++ (false::false::left)) true
      ([true,false,true] ++ right), -2, 1) := by rfl

/-- Arbitrarily long E/1 one sweeps never exceed their entry head. -/
private theorem sweep_max (n : Nat) (left right : List Bool) :
    runWithMax n (z 4 (ones n ++ left) true right) =
    some (z 4 left true (ones n ++ right), -((n:Nat):Int), 0) := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
    have hfirst : runWithMax 1
        (z 4 (ones (n+1) ++ left) true right) =
      some (z 4 (ones n ++ left) true (true::right), -1, 0) := by rfl
    rw [show n+1=1+n by omega, runWithMax_add,
      show 1+n=n+1 by omega, hfirst]
    simp only [Option.bind_some]
    rw [ih]
    simp only [Option.map_some]
    have hr : ones n ++ (true::right) = ones (n+1) ++ right := by
      simp [ones,List.replicate_succ',List.append_assoc]
    rw [hr]
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · trivial
    · constructor <;> omega

/-- The twelve-step finishing macro moves net four cells right, with
    the head never exceeding that endpoint, irrespective of remote tails. -/
private theorem tail12_max (left right : List Bool) :
    runWithMax 12 (z 4 (false::false::left) true (ones 4 ++ right)) =
    some (z 0 (ones 6 ++ left) true right, 4, 4) := by rfl

/-- A complete C/0 corridor for every k and arbitrary remote tape has
    exact maximum head displacement +1, final displacement -(2k+2),
    and the specified whole-tape endpoint in 2k+22 primitive steps. -/
theorem czero_context_max (k : Nat) (left right : List Bool) :
    runWithMax (2*k+22)
      (z 2 (true::false::(ones (2*k+4) ++ (false::false::left)))
         false (false::right)) =
    some (z 0 (ones 6 ++ left) true
      (ones (2*k+1) ++ (false::true::right)),
       -((2*k+2 : Nat) : Int), 1) := by
  have hfirst := first_max (2*k+4) left right
  have hsweep := sweep_max (2*k+4) (false::false::left)
    ([true,false,true] ++ right)
  have htail := tail12_max left
    (ones (2*k) ++ ([true,false,true] ++ right))
  have htime : 2*k+22 = 6+((2*k+4)+12) := by omega
  rw [htime,runWithMax_add,hfirst]
  simp only [Option.bind_some]
  rw [runWithMax_add,hsweep]
  simp only [Option.map_some,Option.bind_some]
  have hw : ones (2*k+4) ++ ([true,false,true] ++ right) =
    ones 4 ++ (ones (2*k) ++ ([true,false,true] ++ right)) := by
      rw [show 2*k+4=4+2*k by omega]
      simp [ones, ← List.replicate_append_replicate, List.append_assoc]
  rw [hw,htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · simp [ones, ← List.replicate_append_replicate, List.append_assoc]
  · constructor <;> omega

#print axioms czero_context_max
end BB429CZeroContextMax
