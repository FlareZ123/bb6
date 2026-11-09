import CZeroContext
import W4HeadMax
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429CZeroHeadFrontier
open BB429OddExcursion BB429CZeroEvenReturn BB429CZeroContext BB429W4HeadMax

private theorem ones_split2 (k : Nat) (tail : List Bool) :
    ones (2*(k+1)) ++ tail = true::true::(ones (2*k) ++ tail) := by
  simp only [ones]
  rw [show 2*(k+1)=2+2*k by omega,
    ← List.replicate_append_replicate]
  rfl

private theorem tens_append_two (n : Nat) (r : List Bool) :
    tens n ++ (true::false::r) = tens (n+1) ++ r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change true::false::(tens n ++ (true::false::r)) =
        true::false::(tens (n+1) ++ r)
      rw [ih]

private theorem af_pair_max (left right : List Bool) :
    runWithMax 2 (z 0 (true::true::left) true right) =
      some (z 0 left true (true::false::right),-2,0) := by rfl

/-- Every A/1,F/1 pair makes two left moves, leaving the head max at entry. -/
private theorem af_pairs_max (k : Nat) (tail right : List Bool) :
    runWithMax (2*k) (z 0 (ones (2*k) ++ tail) true right) =
      some (z 0 tail true (tens k ++ right),-((2*k:Nat):Int),0) := by
  induction k generalizing tail right with
  | zero => rfl
  | succ k ih =>
      have h1 : runWithMax 2
          (z 0 (ones (2*(k+1)) ++ tail) true right) =
            some (z 0 (ones (2*k) ++ tail) true (true::false::right),-2,0) := by
        rw [ones_split2]
        exact af_pair_max _ _
      have h1' : runWithMax 2
          (z 0 (ones (2+2*k) ++ tail) true right) =
            some (z 0 (ones (2*k) ++ tail) true (true::false::right),-2,0) := by
        simpa only [show 2+2*k=2*(k+1) by omega] using h1
      rw [show 2*(k+1)=2+2*k by omega,runWithMax_add,h1']
      simp only [Option.bind_some]
      rw [ih tail (true::false::right)]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · exact congrArg (fun r => z 0 tail true r) (tens_append_two k right)
      constructor <;> simp <;> omega

private theorem ar_pair_max (left right : List Bool) :
    runWithMax 2 (z 0 left false (true::false::right)) =
      some (z 0 (true::true::left) false right,2,2) := by rfl

/-- The alternating A/0,B/1 sweep is monotone right by two per pair. -/
private theorem ar_pairs_max (k : Nat) (tail right : List Bool) :
    runWithMax (2*k) (z 0 tail false (tens k ++ right)) =
      some (z 0 (ones (2*k) ++ tail) false right,((2*k:Nat):Int),((2*k:Nat):Int)) := by
  induction k generalizing tail with
  | zero => rfl
  | succ k ih =>
      have h1 : runWithMax 2 (z 0 tail false (tens (k+1) ++ right)) =
          some (z 0 (true::true::tail) false (tens k ++ right),2,2) := by
        exact ar_pair_max tail (tens k ++ right)
      rw [show 2*(k+1)=2+2*k by omega,runWithMax_add,h1]
      simp only [Option.bind_some]
      rw [ih (true::true::tail)]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      constructor
      · have hw : ones (2*k) ++ (true::true::tail) =
            ones (2+2*k) ++ tail := by
          calc
            ones (2*k) ++ (true::true::tail) =
                (ones (2*k) ++ ones 2) ++ tail := by simp [ones, List.append_assoc]
            _ = ones (2*k+2) ++ tail := by
              change (List.replicate (2*k) true ++ List.replicate 2 true) ++ tail = _
              rw [List.replicate_append_replicate]
            _ = ones (2+2*k) ++ tail := by
              rw [show 2*k+2=2+2*k by omega]
        exact congrArg (fun l => z 0 l false right) hw
      constructor <;> simp <;> omega

private theorem ones_split1 (k : Nat) (tail : List Bool) :
    ones (2*k+2) ++ (false::tail) =
      true :: (ones (2*k) ++ (true::false::tail)) := by
  have hfirst : ones (2*k+2) = true :: ones (2*k+1) := by
    change List.replicate (2*k+2) true = _
    rw [show 2*k+2=(2*k+1)+1 by omega, List.replicate_succ]
  have hlast : ones (2*k+1) = ones (2*k) ++ [true] := by
    change List.replicate (2*k+1) true = _
    rw [show 2*k+1=2*k+1 by omega, ← List.replicate_append_replicate]
    rfl
  rw [hfirst,hlast]
  simp [List.append_assoc]

private theorem c0_first_two_max (k : Nat) (tail : List Bool) :
    runWithMax 2 (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 4 (ones (2*k+2) ++ (false::tail)) false [true],0,1) := by rfl

private theorem e0_turn_one_max (k : Nat) (tail : List Bool) :
    runWithMax 1 (z 4 (ones (2*k+2) ++ (false::tail)) false [true]) =
      some (z 0 (ones (2*k) ++ (true::false::tail)) true [false,true],-1,0) := by
  rw [ones_split1]
  rfl

private theorem apair_low_max (k : Nat) (tail : List Bool) :
    runWithMax 2 (z 0 (true::false::tail) true (tens k ++ [false,true])) =
      some (z 0 tail false (tens (k+1) ++ [false,true]),-2,0) := by rfl

private theorem a_even_end_max (k : Nat) (tail : List Bool) :
    runWithMax 2 (z 0 (ones (2*(k+1)) ++ tail) false [false,true]) =
      some (z 2 (ones (2*k+4) ++ tail) true [],2,2) := by
  have hw : ones (2*k+4) = true::true::ones (2*(k+1)) := by
    simp only [ones]
    rw [show 2*k+4=2+2*(k+1) by omega,
      ← List.replicate_append_replicate]
    rfl
  rw [hw]
  rfl

private theorem c1_final_two_max (k : Nat) (tail : List Bool) :
    runWithMax 2 (z 2 (ones (2*k+4) ++ tail) true []) =
      some (z 2 (true::false::(ones (2*k+4) ++ tail)) false [],2,2) := by rfl

/-- Every primitive prefix of this even C/0 return stays at most three
    cells right of entry, and the final C/0 attains that new maximum. -/
theorem even_C0_context_max (k : Nat) (tail : List Bool) :
    runWithMax (4*k+11) (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 2 (true::false::(ones (2*k+4) ++ tail)) false [],3,3) := by
  have h0 := c0_first_two_max k tail
  have h1 := e0_turn_one_max k tail
  have h2 := af_pairs_max k (true::false::tail) [false,true]
  have h3 := apair_low_max k tail
  have h4 := ar_pairs_max (k+1) tail [false,true]
  have h5 := a_even_end_max k tail
  have h6 := c1_final_two_max k tail
  rw [show 4*k+11 = 2+(1+(2*k+(2+(2*(k+1)+(2+2))))) by omega,
    runWithMax_add,h0]
  simp only [Option.bind_some]
  rw [runWithMax_add,h1]
  simp only [Option.bind_some]
  rw [runWithMax_add,h2]
  simp only [Option.bind_some]
  rw [runWithMax_add,h3]
  simp only [Option.bind_some]
  rw [runWithMax_add,h4]
  simp only [Option.bind_some]
  rw [runWithMax_add,h5]
  simp only [Option.bind_some]
  rw [h6]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  constructor <;> simp [Int.natCast_add,Int.natCast_mul] <;> omega

#print axioms even_C0_context_max
end BB429CZeroHeadFrontier
