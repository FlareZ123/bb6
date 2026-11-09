import Low5Delta
import BB429FinishScanEDelta
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429LowOddCore
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429Low5Delta

def blocks : Nat → List Bool
 | 0 => []
 | n+1 => blocks n ++ [true,true,false,true]

def pairs10 : Nat → List Bool
 | 0 => []
 | n+1 => true::false::pairs10 n

private theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  simp [ones]
private theorem pairs01_add (m n : Nat) : pairs01 (m+n) = pairs01 m ++ pairs01 n := by
  induction m with
  | zero => simp [pairs01]
  | succ m ih => simp [pairs01,ih,Nat.succ_add]

private theorem six_contract (tail suffix : List Bool) :
    runWithDelta 6 (z 4 (false::tens 2 ++ tail) true suffix) =
      some (z 4 (false::tail) true ([true,true,false,true]++suffix), -4) := by rfl

private theorem sixteen_entry (suffix : List Bool) :
    runWithDelta 16 (z 4 (false::ones 6) true suffix) =
      some (z 2 (ones 8) true suffix, 0) := by rfl

private theorem eight_burst (tail suffix : List Bool) :
    runWithDelta 8 (z 2 tail true ([true,true,false,true]++suffix)) =
      some (z 2 (ones 4++tail) true suffix,4) := by rfl

private theorem a1_to_c1_21 (rest : List Bool) :
    runWithDelta 21 (z 0 (ones 6) true (true::(pairs01 3 ++ rest))) =
      some (z 2 (ones 6) true (pairs01 5 ++ rest), -3) := by rfl

private theorem c1_pair (l r : List Bool) :
    runWithDelta 2 (z 2 l true (false::true::r)) =
      some (z 2 (true::false::l) true r, 2) := by rfl

private theorem c1_final (l r : List Bool) :
    runWithDelta 2 (z 2 l true (true::true::r)) =
      some (z 0 (true::false::l) true r, 2) := by rfl

theorem blocks_sweep (n : Nat) (left suffix : List Bool) :
  runWithDelta (8*n) (z 2 left true (blocks n ++ suffix)) =
    some (z 2 (ones (4*n) ++ left) true suffix, ((4*n:Nat):Int)) := by
  induction n generalizing left suffix with
  | zero => rfl
  | succ n ih =>
    have hwords : blocks (n+1) ++ suffix =
        blocks n ++ ([true,true,false,true] ++ suffix) := by
      simp [blocks,List.append_assoc]
    have hp := ih left ([true,true,false,true]++suffix)
    have h8 := eight_burst (ones (4*n)++left) suffix
    rw [show 8*(n+1)=8*n+8 by omega,hwords,runWithDelta_add,hp]
    simp only [Option.bind_some]
    rw [h8]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rw [show 4*(n+1)=4+(4*n) by omega,ones_add]
      simp [List.append_assoc]
    · omega

private theorem tens_add (m n : Nat) : tens (m+n) = tens m ++ tens n := by
  induction m with
  | zero => simp [tens]
  | succ m ih =>
    rw [Nat.succ_add]
    change true::false::tens (m+n) = true::false::(tens m ++ tens n)
    rw [ih]

theorem e1_left_contract (n : Nat) (tail suffix : List Bool) :
  runWithDelta (6*n) (z 4 (false::(tens (2*n) ++ tail)) true suffix) =
    some (z 4 (false::tail) true (blocks n ++ suffix), -((4*n:Nat):Int)) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
    have hword : tens (2*(n+1)) = tens 2 ++ tens (2*n) := by
      change tens (2*(n+1)) = [true,false,true,false] ++ tens (2*n)
      rw [show 2*(n+1)=2+(2*n) by omega, tens_add]
      rfl
    have h6 : runWithDelta 6
        (z 4 (false::(tens (2*(n+1)) ++ tail)) true suffix) =
        some (z 4 (false::(tens (2*n) ++ tail)) true
          ([true,true,false,true]++suffix), -4) := by
      rw [hword]
      change runWithDelta 6
        (z 4 (false::tens 2 ++ (tens (2*n) ++ tail)) true suffix) = _
      exact six_contract (tens (2*n)++tail) suffix
    have hrem := ih ([true,true,false,true]++suffix)
    rw [show 6*(n+1)=6+6*n by omega,runWithDelta_add,h6]
    simp only [Option.bind_some]
    rw [hrem]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · congr 1
      simp [blocks,List.append_assoc]
    · omega

private theorem pairs10_right (n : Nat) :
    pairs10 n ++ [true,false] = pairs10 (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true::false::(pairs10 n ++ [true,false]) =
      true::false::pairs10 (n+1)
    rw [ih]

theorem c1_pairs_delta (n : Nat) (left suffix : List Bool) :
  runWithDelta (2*n) (z 2 left true (pairs01 n ++ suffix)) =
    some (z 2 (pairs10 n ++ left) true suffix, ((2*n:Nat):Int)) := by
  induction n generalizing left suffix with
  | zero => rfl
  | succ n ih =>
    have h2 : runWithDelta 2
        (z 2 left true (pairs01 (n+1) ++ suffix)) =
        some (z 2 (true::false::left) true (pairs01 n ++ suffix),2) := by
      change runWithDelta 2 (z 2 left true (false::true::(pairs01 n++suffix))) = _
      exact c1_pair left (pairs01 n++suffix)
    rw [show 2*(n+1)=2+2*n by omega,runWithDelta_add,h2]
    simp only [Option.bind_some]
    rw [ih (true::false::left) suffix]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · have hw : pairs10 n ++ (true::false::left) =
          pairs10 (n+1) ++ left := by
        calc
          pairs10 n ++ (true::false::left) =
              (pairs10 n ++ [true,false]) ++ left := by rw [List.append_assoc]; rfl
          _ = pairs10 (n+1) ++ left := by rw [pairs10_right]
      exact congrArg (fun l : List Bool => z 2 l true suffix) hw
    · omega

private theorem pairs10_to_junc (n : Nat) :
  pairs10 n ++ ones 6 = true :: (pairs01 n ++ ones 5) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true :: false :: (pairs10 n ++ ones 6) =
      true :: false :: true :: (pairs01 n ++ ones 5)
    rw [ih]

theorem a1_to_junc_general (n : Nat) (suffix : List Bool) :
  runWithDelta (4*n+33)
    (z 0 (ones 6) true (true::(pairs01 (2*n+3) ++ (ones 4 ++ suffix)))) =
  some (z 0 (true::(pairs01 (2*n+6) ++ ones 5)) true
    (ones 2 ++ suffix), ((4*n+9:Nat):Int)) := by
  have hp : pairs01 (2*n+3) = pairs01 3 ++ pairs01 (2*n) := by
    rw [show 2*n+3=3+2*n by omega,pairs01_add]
  have h21 : runWithDelta 21
      (z 0 (ones 6) true (true::(pairs01 (2*n+3) ++ (ones 4 ++ suffix)))) =
      some (z 2 (ones 6) true
        (pairs01 (2*n+5) ++ (ones 4 ++ suffix)), -3) := by
    rw [hp,List.append_assoc]
    have h0 := a1_to_c1_21 (pairs01 (2*n) ++ (ones 4 ++ suffix))
    have hr : pairs01 5 ++ (pairs01 (2*n) ++ (ones 4 ++ suffix)) =
        pairs01 (2*n+5) ++ (ones 4 ++ suffix) := by
      rw [← List.append_assoc, ← pairs01_add]
      rw [show 5+2*n=2*n+5 by omega]
    rw [hr] at h0
    exact h0
  have hpair := c1_pairs_delta (2*n+5) (ones 6) (ones 4 ++ suffix)
  have hlast : runWithDelta 2
      (z 2 (pairs10 (2*n+5) ++ ones 6) true (ones 4 ++ suffix)) =
      some (z 0 (true::(pairs01 (2*n+6) ++ ones 5)) true (ones 2 ++ suffix),2) := by
    have hz := c1_final (pairs10 (2*n+5) ++ ones 6) (ones 2 ++ suffix)
    have hw : ones 4 ++ suffix = true::true::(ones 2 ++ suffix) := by rfl
    rw [hw]
    have hl : true::false::(pairs10 (2*n+5) ++ ones 6) =
        true::(pairs01 (2*n+6) ++ ones 5) := by
      have hsrc := pairs10_to_junc (2*n+6)
      have hcons : pairs10 (2*n+6) = true::false::pairs10 (2*n+5) := by
        rw [show 2*n+6=(2*n+5)+1 by omega]
        rfl
      rw [hcons] at hsrc
      exact hsrc
    rw [hl] at hz
    exact hz
  rw [show 4*n+33=21+((2*(2*n+5))+2) by omega,runWithDelta_add,h21]
  simp only [Option.bind_some]
  rw [runWithDelta_add,hpair]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,true_and]
  omega

theorem c1_to_junc_general (n : Nat) (suffix : List Bool) :
  runWithDelta (8*n+47)
    (z 2 (ones (4*n+8)) true (ones 9 ++ suffix)) =
    some (z 0 (true::(pairs01 (2*n+6) ++ ones 5)) true
      (ones 2 ++ suffix), 7) := by
  have h12 : runWithDelta 12
      (z 2 (ones (4*n+8)) true (ones 9 ++ suffix)) =
      some (z 0 (ones (4*n+8)) true
        (true::(pairs01 2 ++ (true::(ones 3 ++ suffix)))),0) := by
    have hwords : ones 9 ++ suffix = ones 6 ++ (ones 3 ++ suffix) := by
      rw [← List.append_assoc, ← ones_add]
    rw [hwords]
    exact finishC_to_A_delta (ones (4*n+8)) (ones 3 ++ suffix)
  have hleft : ones (4*n+8) =
      true :: (ones (2*(2*n+1)) ++ ones 5) := by
    have h1 : 4*n+8 = 1+(2*(2*n+1)+5) := by omega
    rw [h1,ones_add,ones_add]
    rfl
  have hshift : runWithDelta (4*n+2)
      (z 0 (ones (4*n+8)) true
        (true::(pairs01 2 ++ (true::(ones 3 ++ suffix))))) =
      some (z 0 (ones 6) true
        (true::(pairs01 (2*n+3) ++ (ones 4 ++ suffix))),
        -((4*n+2:Nat):Int)) := by
    have h0 := shift_A11_delta (2*n+1) (ones 5)
      (pairs01 2 ++ (true::(ones 3 ++ suffix)))
    have hr : pairs01 (2*n+1) ++
          (pairs01 2 ++ (true::(ones 3 ++ suffix))) =
        pairs01 (2*n+3) ++ (ones 4 ++ suffix) := by
      rw [← List.append_assoc, ← pairs01_add]
      rw [show (2*n+1)+2=2*n+3 by omega]
      rfl
    rw [hleft, show 4*n+2=2*(2*n+1) by omega]
    rw [hr] at h0
    simpa only [show ones 6 = true::ones 5 by rfl] using h0
  have hlast := a1_to_junc_general n suffix
  rw [show 8*n+47=12+((4*n+2)+(4*n+33)) by omega,
    runWithDelta_add,h12]
  simp only [Option.bind_some]
  rw [runWithDelta_add,hshift]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,true_and]
  omega

theorem e1_even_to_junc (n : Nat) (suffix : List Bool) :
  runWithDelta (22*n+63)
    (z 4 (false::(tens (2*n) ++ ones 6)) true (ones 9 ++ suffix)) =
    some (z 0 (true::(pairs01 (2*n+6) ++ ones 5)) true
      (ones 2 ++ suffix), 7) := by
  have h6 := e1_left_contract n (ones 6) (ones 9 ++ suffix)
  have h16 := sixteen_entry (blocks n ++ (ones 9 ++ suffix))
  have h8 := blocks_sweep n (ones 8) (ones 9 ++ suffix)
  have h47 := c1_to_junc_general n suffix
  have hl : ones (4*n) ++ ones 8 = ones (4*n+8) := by
    rw [← ones_add]
  rw [show 22*n+63=6*n+(16+(8*n+(8*n+47))) by omega,
    runWithDelta_add,h6]
  simp only [Option.bind_some]
  rw [runWithDelta_add,h16]
  simp only [Option.bind_some]
  rw [runWithDelta_add,h8]
  simp only [Option.bind_some]
  rw [hl,h47]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,true_and]
  omega

#print axioms blocks_sweep
#print axioms e1_left_contract
#print axioms a1_to_junc_general
#print axioms e1_even_to_junc
end BB429LowOddCore
