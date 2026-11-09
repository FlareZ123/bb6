import CZeroContextToE1
import W4CZeroCount
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429CZeroCensus
open BB429OddExcursion BB429CZeroEvenReturn BB429CZeroContext
open BB429CZeroContextToE1 BB429W4CZeroCount

private theorem ones_split2 (k : Nat) (tail : List Bool) :
    ones (2*(k+1)) ++ tail = true::true::(ones (2*k) ++ tail) := by
  simp only [ones]
  rw [show 2*(k+1)=2+2*k by omega,←List.replicate_append_replicate]
  rfl

private theorem tens_append_two (n : Nat) (r : List Bool) :
    tens n ++ (true::false::r) = tens (n+1) ++ r := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change true::false::(tens n ++ (true::false::r)) =
        true::false::(tens (n+1) ++ r)
      rw [ih]

private theorem af_pair_count (left right : List Bool) :
    runCount 2 (z 0 (true::true::left) true right) =
      some (z 0 left true (true::false::right),0) := by rfl

private theorem af_pairs_count (k : Nat) (tail right : List Bool) :
    runCount (2*k) (z 0 (ones (2*k) ++ tail) true right) =
      some (z 0 tail true (tens k ++ right),0) := by
  induction k generalizing tail right with
  | zero => rfl
  | succ k ih =>
      have h1 : runCount 2 (z 0 (ones (2+2*k) ++ tail) true right) =
          some (z 0 (ones (2*k) ++ tail) true (true::false::right),0) := by
        rw [show 2+2*k=2*(k+1) by omega,ones_split2]
        exact af_pair_count _ _
      rw [show 2*(k+1)=2+2*k by omega,runCount_add,h1]
      simp only [Option.bind_some]
      rw [ih tail (true::false::right)]
      simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
      constructor
      · exact congrArg (fun r => z 0 tail true r) (tens_append_two k right)
      · trivial

private theorem ar_pair_count (left right : List Bool) :
    runCount 2 (z 0 left false (true::false::right)) =
      some (z 0 (true::true::left) false right,0) := by rfl

private theorem ar_pairs_count (k : Nat) (tail right : List Bool) :
    runCount (2*k) (z 0 tail false (tens k ++ right)) =
      some (z 0 (ones (2*k) ++ tail) false right,0) := by
  induction k generalizing tail with
  | zero => rfl
  | succ k ih =>
      have h1 : runCount 2 (z 0 tail false (tens (k+1) ++ right)) =
          some (z 0 (true::true::tail) false (tens k ++ right),0) := by
        exact ar_pair_count tail (tens k ++ right)
      rw [show 2*(k+1)=2+2*k by omega,runCount_add,h1]
      simp only [Option.bind_some]
      rw [ih (true::true::tail)]
      simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
      constructor
      · have hw : ones (2*k) ++ (true::true::tail) = ones (2+2*k) ++ tail := by
          calc
            ones (2*k) ++ (true::true::tail) =
                (ones (2*k) ++ ones 2) ++ tail := by simp [ones,List.append_assoc]
            _ = ones (2*k+2) ++ tail := by
              change (List.replicate (2*k) true ++ List.replicate 2 true) ++ tail = _
              rw [List.replicate_append_replicate]
            _ = ones (2+2*k) ++ tail := by
              rw [show 2*k+2=2+2*k by omega]
        exact congrArg (fun l => z 0 l false right) hw
      · trivial

private theorem ones_split1 (k : Nat) (tail : List Bool) :
    ones (2*k+2) ++ (false::tail) =
      true :: (ones (2*k) ++ (true::false::tail)) := by
  have hfirst : ones (2*k+2) = true :: ones (2*k+1) := by
    change List.replicate (2*k+2) true = _
    rw [show 2*k+2=(2*k+1)+1 by omega,List.replicate_succ]
  have hlast : ones (2*k+1) = ones (2*k) ++ [true] := by
    change List.replicate (2*k+1) true = _
    rw [show 2*k+1=2*k+1 by omega,←List.replicate_append_replicate]
    rfl
  rw [hfirst,hlast]
  simp [List.append_assoc]

private theorem first_two_count (k : Nat) (tail : List Bool) :
    runCount 2 (z 2 (ones (2*k+2) ++ false::tail) false []) =
      some (z 4 (ones (2*k+2) ++ false::tail) false [true],1) := by rfl

private theorem e0_turn_count (k : Nat) (tail : List Bool) :
    runCount 1 (z 4 (ones (2*k+2) ++ false::tail) false [true]) =
      some (z 0 (ones (2*k) ++ (true::false::tail)) true [false,true],0) := by
  rw [ones_split1]
  rfl

private theorem apair_low_count (k : Nat) (tail : List Bool) :
    runCount 2 (z 0 (true::false::tail) true (tens k ++ [false,true])) =
      some (z 0 tail false (tens (k+1) ++ [false,true]),0) := by rfl

private theorem a_even_end_count (k : Nat) (tail : List Bool) :
    runCount 2 (z 0 (ones (2*(k+1)) ++ tail) false [false,true]) =
      some (z 2 (ones (2*k+4) ++ tail) true [],0) := by
  have hw : ones (2*k+4) = true::true::ones (2*(k+1)) := by
    simp only [ones]
    rw [show 2*k+4=2+2*(k+1) by omega,←List.replicate_append_replicate]
    rfl
  rw [hw]
  rfl

private theorem c1_final_count (k : Nat) (tail : List Bool) :
    runCount 2 (z 2 (ones (2*k+4) ++ tail) true []) =
      some (z 2 (true::false::(ones (2*k+4) ++ tail)) false [],0) := by rfl

/-- The even-context return processes only its starting C/0 instruction;
    its endpoint is the next C/0 and is excluded from the count. -/
theorem even_C0_context_exact_one (k : Nat) (tail : List Bool) :
    runCount (4*k+11) (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 2 (true::false::(ones (2*k+4) ++ tail)) false [],1) := by
  have h0 := first_two_count k tail
  have h1 := e0_turn_count k tail
  have h2 := af_pairs_count k (true::false::tail) [false,true]
  have h3 := apair_low_count k tail
  have h4 := ar_pairs_count (k+1) tail [false,true]
  have h5 := a_even_end_count k tail
  have h6 := c1_final_count k tail
  rw [show 4*k+11 = 2+(1+(2*k+(2+(2*(k+1)+(2+2))))) by omega,
    runCount_add,h0]
  simp only [Option.bind_some]
  rw [runCount_add,h1]
  simp only [Option.bind_some]
  rw [runCount_add,h2]
  simp only [Option.bind_some]
  rw [runCount_add,h3]
  simp only [Option.bind_some]
  rw [runCount_add,h4]
  simp only [Option.bind_some]
  rw [runCount_add,h5]
  simp only [Option.bind_some]
  rw [h6]
  rfl

/-- The six-step 10-prefix exit processes only its initial C/0. -/
theorem C0_to_E1_6_count (n : Nat) (tail : List Bool) :
    runCount 6 (z 2 (true::false::(ones n ++ tail)) false []) =
      some (z 4 (ones n ++ tail) true [true,false,true],1) := by rfl

/-- The E/1 left sweep contains no C/0 instruction start. -/
theorem E1_sweep_zero_count (n : Nat) (tail suffix : List Bool) :
    runCount n (z 4 (ones n ++ tail) true suffix) =
      some (z 4 tail true (ones n ++ suffix),0) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      have hfirst : runCount 1 (z 4 (ones (n+1) ++ tail) true suffix) =
          some (z 4 (ones n ++ tail) true (true::suffix),0) := by rfl
      have hwords : ones n ++ (true::suffix) = ones (n+1) ++ suffix := by
        simp [ones,List.replicate_succ',List.append_assoc]
      rw [show n+1=1+n by omega,runCount_add,
        show 1+n=n+1 by omega,hfirst]
      simp only [Option.bind_some]
      rw [ih (true::suffix),hwords]
      rfl

/-- Exactly one C/0, at entry, precedes the deep E/1 boundary. -/
theorem C0_to_E1_context_count (k : Nat) (tail : List Bool) :
    runCount (2*k+10) (z 2 (true::false::(ones (2*k+4) ++ tail)) false []) =
      some (z 4 tail true (ones (2*k+4) ++ [true,false,true]),1) := by
  rw [show 2*k+10=6+(2*k+4) by omega,
    runCount_add,C0_to_E1_6_count]
  simp only [Option.bind_some]
  rw [E1_sweep_zero_count]
  rfl

/-- Two and only two C/0 instruction starts in the entire 6k+21-step
    arbitrary-context corridor to E/1, both at successive right records. -/
theorem even_C0_to_E1_exact_two (k : Nat) (tail : List Bool) :
    runCount (6*k+21) (z 2 (ones (2*k+2) ++ (false::tail)) false []) =
      some (z 4 tail true (ones (2*k+4) ++ [true,false,true]),2) := by
  rw [show 6*k+21=(4*k+11)+(2*k+10) by omega,
    runCount_add,even_C0_context_exact_one]
  simp only [Option.bind_some]
  rw [C0_to_E1_context_count]
  rfl

/-- Public C/0-free A/F induction, for arbitrary uninspected context. -/
theorem af_pairs_no_czero (k : Nat) (tail right : List Bool) :
    runCount (2*k) (z 0 (ones (2*k) ++ tail) true right) =
    some (z 0 tail true (tens k ++ right),0) :=
  af_pairs_count k tail right

/-- Public C/0-free A/B induction, exact complete context. -/
theorem ar_pairs_no_czero (k : Nat) (tail right : List Bool) :
    runCount (2*k) (z 0 tail false (tens k ++ right)) =
    some (z 0 (ones (2*k) ++ tail) false right,0) :=
  ar_pairs_count k tail right

#print axioms af_pairs_no_czero
#print axioms ar_pairs_no_czero

#print axioms C0_to_E1_context_count
#print axioms even_C0_to_E1_exact_two
#print axioms even_C0_context_exact_one
end BB429CZeroCensus
