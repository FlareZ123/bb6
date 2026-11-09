import Low3Delta
import BB429FinishScanEDelta
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 30000000

namespace BB429Low5Delta
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429Low3Delta

/-- The entire prepared deficit-five zipper after v+1 physical bubbles. -/
def stage5 (v : Nat) : Zipper :=
  z 0 (ones (4*v+4) ++ (true::false::true::false::ones 6)) true [false,true]

/-- An arbitrary-suffix fixed 63-step low-five boundary transfer. -/
theorem tail63 (suffix : List Bool) :
  runWithDelta 63 (z 4 (false :: ones 6) true (ones 9 ++ suffix)) =
    some (z 0 (true :: (pairs01 6 ++ ones 5)) true (ones 2 ++ suffix), 7) := by rfl

private theorem af_tail_delta (l r : List Bool) :
  runWithDelta 2 (z 0 (true::false::l) true r) =
    some (z 0 l false (true::false::r), -2) := by rfl

private theorem low3_tail_delta (l : List Bool) :
  runWithDelta 4 (z 0 l false [false,true]) =
    some (z 2 (true::false::true::true::l) false [], 4) := by rfl

private theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  simp [ones]

private theorem e1_sweep_delta (n : Nat) (tail suffix : List Bool) :
  runWithDelta n (z 4 (ones n ++ tail) true suffix) =
    some (z 4 tail true (ones n ++ suffix), -((n:Nat):Int)) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
    have hfirst : runWithDelta 1 (z 4 (ones (n+1) ++ tail) true suffix) =
        some (z 4 (ones n ++ tail) true (true::suffix), -1) := by rfl
    rw [show n+1=1+n by omega,runWithDelta_add]
    simp only [show 1+n=n+1 by omega]
    rw [hfirst]
    simp only [Option.bind_some]
    rw [ih]
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
    constructor
    · congr 1
      simp [ones,List.replicate_succ',List.append_assoc]
    · omega

private theorem c0_to_e1_delta (n : Nat) (tail : List Bool) :
  runWithDelta 6 (z 2 (true::false::(ones n ++ tail)) false []) =
    some (z 4 (ones n ++ tail) true [true,false,true], -2) := by rfl

/-- Unbounded C/0 to Junc(6,0,4v+2) exactly, with signed displacement. -/
theorem c0_to_junc6_delta (v : Nat) :
    runWithDelta (4*v+78)
      (z 2 (true::false::(ones (4*v+9) ++ (false::ones 6))) false []) =
      some (junc 6 0 (4*v+2), -((4*v+4 : Nat):Int)) := by
  have h1 := c0_to_e1_delta (4*v+9) (false::ones 6)
  have h2 := e1_sweep_delta (4*v+9) (false::ones 6) [true,false,true]
  have hright : ones (4*v+9) ++ [true,false,true] =
       ones 9 ++ (ones (4*v) ++ [true,false,true]) := by
    rw [show 4*v+9=9+4*v by omega, ones_add, List.append_assoc]
  have h3 : runWithDelta 63
      (z 4 (false::ones 6) true (ones (4*v+9) ++ [true,false,true])) =
      some (z 0 (true :: (pairs01 6 ++ ones 5)) true
        (ones 2 ++ (ones (4*v) ++ [true,false,true])),7) := by
    rw [hright]
    exact tail63 (ones (4*v) ++ [true,false,true])
  have htarget : z 0 (true::(pairs01 6 ++ ones 5)) true
       (ones 2 ++ (ones (4*v) ++ [true,false,true])) =
       junc 6 0 (4*v+2) := by
    simp only [junc,pairs01,List.nil_append]
    have hw : ones 2 ++ (ones (4*v) ++ [true,false,true]) =
        true :: (ones (4*v+2) ++ [false,true]) := by
      rw [← List.append_assoc, ← ones_add]
      rw [show 2+4*v = (4*v+2) by omega]
      have hones : ones (4*v+2) ++ [true] = true :: ones (4*v+2) := by
        change ones (4*v+2) ++ ones 1 = true :: ones (4*v+2)
        rw [← ones_add]
        rw [show 4*v+2+1=1+(4*v+2) by omega,ones_add]
        rfl
      rw [show ([true,false,true]:List Bool)=[true]++[false,true] by rfl,
        ← List.append_assoc, hones]
      rfl
    exact congrArg (fun r : List Bool => z 0 (true::(pairs01 6 ++ ones 5)) true r) hw
  have ht : 4*v+78=6+((4*v+9)+63) := by omega
  rw [ht,runWithDelta_add,h1]
  simp only [Option.bind_some]
  rw [runWithDelta_add,h2]
  simp only [Option.bind_some]
  rw [h3]
  simp only [Option.map_some]
  rw [← htarget]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  omega

/-- The first source section is an exact C/0 corridor with delta +4. -/
theorem stage5_to_C0_delta (v : Nat) :
    runWithDelta (8*v+16) (stage5 v) =
      some (z 2 (true::false::(ones (4*v+9) ++ (false::ones 6))) false [],4) := by
  have hAF : runWithDelta (4*v+4) (stage5 v) =
      some (z 0 (true::false::true::false::ones 6) true
        (tens (2*v+2) ++ [false,true]), -((4*v+4:Nat):Int)) := by
    simpa [stage5,ones, show 2*(2*v+2)=4*v+4 by omega] using
      (af_pairs_delta (2*v+2) (true::false::true::false::ones 6) [false,true])
  have h2 : runWithDelta 2
      (z 0 (true::false::true::false::ones 6) true (tens (2*v+2)++[false,true])) =
      some (z 0 (true::false::ones 6) false
        (tens (2*v+3)++[false,true]),-2) := by
    change runWithDelta 2
      (z 0 (true::false::true::false::ones 6) true (tens (2*v+2)++[false,true])) =
      some (z 0 (true::false::ones 6) false
        (true::false::(tens (2*v+2)++[false,true])),-2)
    exact af_tail_delta (true::false::ones 6) _
  have hAR : runWithDelta (4*v+6)
      (z 0 (true::false::ones 6) false (tens (2*v+3)++[false,true])) =
      some (z 0 (ones (4*v+6)++(true::false::ones 6)) false [false,true],
        ((4*v+6:Nat):Int)) := by
    simpa [show 2*(2*v+3)=4*v+6 by omega] using
      (ar_pairs_delta (2*v+3) (true::false::ones 6) [false,true])
  have h4 : runWithDelta 4
      (z 0 (ones (4*v+6)++(true::false::ones 6)) false [false,true]) =
      some (z 2 (true::false::(ones (4*v+9) ++ (false::ones 6))) false [],4) := by
    have hw : true::true::(ones (4*v+6) ++ (true::false::ones 6)) =
        ones (4*v+9) ++ (false::ones 6) := by
      calc
        true::true::(ones (4*v+6) ++ (true::false::ones 6)) =
            ((ones 2 ++ ones (4*v+6)) ++ ones 1) ++ (false::ones 6) := by simp [ones, List.append_assoc]
        _ = ones (2+(4*v+6)+1) ++ (false::ones 6) := by
          rw [← ones_add, ← ones_add]
        _ = ones (4*v+9) ++ (false::ones 6) := by
          rw [show 2+(4*v+6)+1=4*v+9 by omega]
    rw [← hw]
    exact low3_tail_delta _
  rw [show 8*v+16=(4*v+4)+(2+((4*v+6)+4)) by omega,runWithDelta_add,hAF]
  simp only [Option.bind_some]
  rw [runWithDelta_add,h2]
  simp only [Option.bind_some]
  rw [runWithDelta_add,hAR]
  simp only [Option.bind_some]
  rw [h4]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,true_and]
  omega

/-- Exact all-parameter prepared low-five symbolic return, including head displacement. -/
theorem stage5_to_junc_delta (v : Nat) :
    runWithDelta (12*v+94) (stage5 v) =
      some (junc 6 0 (4*v+2), -((4*v:Nat):Int)) := by
  have hc := stage5_to_C0_delta v
  have hj := c0_to_junc6_delta v
  rw [show 12*v+94=(8*v+16)+(4*v+78) by omega,
    runWithDelta_add,hc]
  simp only [Option.bind_some]
  rw [hj]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq,true_and]
  omega

#print axioms tail63
#print axioms c0_to_junc6_delta
#print axioms stage5_to_C0_delta
#print axioms stage5_to_junc_delta
end BB429Low5Delta
