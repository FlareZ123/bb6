import BB429FinishScanEDelta
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low3Delta
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta

/-- Source configuration after (v+1) negative-even hole bubbles. -/
def stage3 (v : Nat) : Zipper :=
  z 0 (ones (4*v+4) ++ (true::false::ones 6)) true [false,true]

private theorem ones_add (m n : Nat) :
    ones (m+n) = ones m ++ ones n := by simp [ones]

private theorem af_two_delta (l r : List Bool) :
    runWithDelta 2 (z 0 (true::true::l) true r) =
      some (z 0 l true (true::false::r), -2) := by rfl

private theorem ar_two_delta (l r : List Bool) :
    runWithDelta 2 (z 0 l false (true::false::r)) =
      some (z 0 (true::true::l) false r, 2) := by rfl

/-- Each consumed A/F pair moves the physical head two positions left. -/
theorem af_pairs_delta (j : Nat) (l r : List Bool) :
    runWithDelta (2*j) (z 0 (ones (2*j) ++ l) true r) =
      some (z 0 l true (tens j ++ r), -((2*j : Nat) : Int)) := by
  induction j generalizing l r with
  | zero => rfl
  | succ j ih =>
      have hrep : ones (2*(j+1)) ++ l =
          ones (2*j) ++ (true::true::l) := by
        change List.replicate (2*(j+1)) true ++ l =
          List.replicate (2*j) true ++ (true::true::l)
        rw [show 2*(j+1)=2*j+2 by omega,
          ← List.replicate_append_replicate]
        simp [List.append_assoc]
      have hpart : runWithDelta (2*(j+1))
          (z 0 (ones (2*(j+1)) ++ l) true r) =
          some (z 0 l true (tens (j+1) ++ r),
              -((2*(j+1) : Nat) : Int)) := by
        rw [hrep, show 2*(j+1)=2*j+2 by omega, runWithDelta_add]
        rw [ih (true::true::l) r]
        simp only [Option.bind_some]
        have ht : runWithDelta 2
            (z 0 (true::true::l) true (tens j ++ r)) =
            some (z 0 l true (tens (j+1) ++ r), -2) := by
          change runWithDelta 2 (z 0 (true::true::l) true (tens j ++ r)) =
            some (z 0 l true (true::false::(tens j ++ r)), -2)
          exact af_two_delta l (tens j ++ r)
        rw [ht]
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
        omega
      exact hpart

/-- Each A/B rightward repaint pair moves the head two positions right. -/
theorem ar_pairs_delta (j : Nat) (l r : List Bool) :
    runWithDelta (2*j) (z 0 l false (tens j ++ r)) =
      some (z 0 (ones (2*j) ++ l) false r, ((2*j : Nat) : Int)) := by
  induction j generalizing l with
  | zero => rfl
  | succ j ih =>
      have hfirst : runWithDelta 2
          (z 0 l false (tens (j+1) ++ r)) =
          some (z 0 (true::true::l) false (tens j ++ r),2) := by
        change runWithDelta 2 (z 0 l false (true::false::(tens j++r))) = _
        exact ar_two_delta l (tens j ++ r)
      have hwords : ones (2*j) ++ (true::true::l) =
          ones (2*(j+1)) ++ l := by
        change List.replicate (2*j) true ++ (true::true::l) =
          List.replicate (2*(j+1)) true ++ l
        rw [show 2*(j+1)=2*j+2 by omega,
          ← List.replicate_append_replicate]
        simp [List.append_assoc]
      rw [show 2*(j+1)=2+2*j by omega, runWithDelta_add, hfirst]
      simp only [Option.bind_some]
      rw [ih (true::true::l),hwords]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
      constructor
      · rw [show 2*(j+1)=2+2*j by omega]
      · omega

private theorem af_tail_delta (l r : List Bool) :
    runWithDelta 2 (z 0 (true::false::l) true r) =
      some (z 0 l false (true::false::r), -2) := by rfl

private theorem low3_tail_delta (l : List Bool) :
    runWithDelta 4 (z 0 l false [false,true]) =
      some (z 2 (true::false::true::true::l) false [], 4) := by rfl

private theorem compose_delta (m n : Nat) (a b c : Zipper) (d e : Int)
    (h1 : runWithDelta m a=some (b,d))
    (h2 : runWithDelta n b=some (c,e)) :
    runWithDelta (m+n) a=some (c,d+e) := by
  rw [runWithDelta_add,h1]
  simp only [Option.bind_some]
  rw [h2]
  rfl

/-- Source segment after the genuine low3 (v+1)-bubble prefix. -/
theorem stage3_to_C0_delta (v : Nat) :
    runWithDelta (8*v+16) (stage3 v) =
      some (z 2 (true::false::ones (4*v+14)) false [],4) := by
  have hAF : runWithDelta (4*v+4) (stage3 v) =
      some (z 0 (true::false::ones 6) true
        (tens (2*v+2) ++ [false,true]), -((4*v+4 : Nat) : Int)) := by
    simpa [stage3,ones,show 2*(2*v+2)=4*v+4 by omega] using
      (af_pairs_delta (2*v+2) (true::false::ones 6) [false,true])
  have h2 : runWithDelta 2
      (z 0 (true::false::ones 6) true (tens (2*v+2) ++ [false,true])) =
      some (z 0 (ones 6) false
        (tens (2*v+3) ++ [false,true]),-2) := by
    change runWithDelta 2 (z 0 (true::false::ones 6) true
      (tens (2*v+2) ++ [false,true])) =
      some (z 0 (ones 6) false
        (true::false::(tens (2*v+2) ++ [false,true])),-2)
    exact af_tail_delta (ones 6) _
  have hAR : runWithDelta (4*v+6) (z 0 (ones 6) false
      (tens (2*v+3) ++ [false,true])) =
      some (z 0 (ones (4*v+6) ++ ones 6) false [false,true],
        ((4*v+6 : Nat) : Int)) := by
    simpa [show 2*(2*v+3)=4*v+6 by omega] using
      (ar_pairs_delta (2*v+3) (ones 6) [false,true])
  have h4 : runWithDelta 4 (z 0 (ones (4*v+6) ++ ones 6)
      false [false,true]) =
      some (z 2 (true::false::ones (4*v+14)) false [],4) := by
    have hw : ones (4*v+14) = true::true::(ones (4*v+6) ++ ones 6) := by
      rw [show 4*v+14=2+((4*v+6)+6) by omega, ones_add,ones_add]
      rfl
    rw [hw]
    exact low3_tail_delta _
  have h12 := compose_delta (4*v+6) 4
    (z 0 (ones 6) false (tens (2*v+3) ++ [false,true]))
    (z 0 (ones (4*v+6) ++ ones 6) false [false,true])
    (z 2 (true::false::ones (4*v+14)) false [])
    ((4*v+6 : Nat) : Int) 4 hAR h4
  have h212 := compose_delta 2 ((4*v+6)+4)
    (z 0 (true::false::ones 6) true (tens (2*v+2) ++ [false,true]))
    (z 0 (ones 6) false (tens (2*v+3) ++ [false,true]))
    (z 2 (true::false::ones (4*v+14)) false [])
    (-2) (((4*v+6 : Nat) : Int)+4) h2 h12
  have hAll := compose_delta (4*v+4) (2+((4*v+6)+4))
    (stage3 v)
    (z 0 (true::false::ones 6) true (tens (2*v+2) ++ [false,true]))
    (z 2 (true::false::ones (4*v+14)) false [])
    (-((4*v+4 : Nat) : Int)) (-2+(((4*v+6 : Nat) : Int)+4))
    hAF h212
  have ht : (4*v+4)+(2+((4*v+6)+4)) = 8*v+16 := by omega
  have hd : -((4*v+4 : Nat) : Int) + (-2+(((4*v+6 : Nat) : Int)+4))=4 := by omega
  simpa only [ht,hd] using hAll

/-- The complete C/0-frontier to Junc0 corridor has exact head shift. -/
private theorem c0_to_e1_delta (n : Nat) :
    runWithDelta 6 (z 2 (true::false::ones n) false []) =
      some (z 4 (ones n) true [true,false,true], -2) := by rfl

private theorem e1_sweep_delta (n : Nat) (suffix : List Bool) :
    runWithDelta n (z 4 (ones n) true suffix) =
      some (z 4 [] true (ones n ++ suffix), -((n:Nat):Int)) := by
  induction n generalizing suffix with
  | zero => rfl
  | succ n ih =>
      have hfirst : runWithDelta 1 (z 4 (ones (n+1)) true suffix) =
          some (z 4 (ones n) true (true::suffix), -1) := by rfl
      have hw : ones n ++ (true::suffix) = ones (n+1) ++ suffix := by
        simp [ones,List.replicate_succ',List.append_assoc]
      have hcomp := runWithDelta_add 1 n (z 4 (ones (n+1)) true suffix)
      have hfirstComp : runWithDelta (n+1) (z 4 (ones (n+1)) true suffix) =
          (runWithDelta 1 (z 4 (ones (n+1)) true suffix)).bind
            (fun p => (runWithDelta n p.1).map (fun q => (q.1,p.2+q.2))) := by
        simpa only [show 1+n=n+1 by omega] using hcomp
      rw [hfirstComp,hfirst]
      simp only [Option.bind_some]
      rw [ih,hw]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and]
      omega

private theorem e1_to_junc12_delta (suffix : List Bool) :
    runWithDelta 12 (z 4 [] true (ones 4 ++ suffix)) =
      some (z 0 (ones 6) true suffix, 4) := by rfl

theorem c0_to_junc0_delta (k : Nat) :
    runWithDelta (2*k+22) (z 2 (true::false::ones (2*k+4)) false []) =
      some (junc 0 0 (2*k), -((2*k+2 : Nat) : Int)) := by
  have hfirst := c0_to_e1_delta (2*k+4)
  have hsweep := e1_sweep_delta (2*k+4) [true,false,true]
  have htail := e1_to_junc12_delta (ones (2*k) ++ [true,false,true])
  have hwords : ones (2*k+4) ++ [true,false,true] =
      ones 4 ++ (ones (2*k) ++ [true,false,true]) := by
    rw [show 2*k+4 = 4+2*k by omega,
      ones_add, List.append_assoc]
  have ht : 2*k+22 = 6+((2*k+4)+12) := by omega
  rw [ht,runWithDelta_add,hfirst]
  simp only [Option.bind_some]
  rw [runWithDelta_add,hsweep]
  simp only [Option.bind_some]
  rw [hwords,htail]
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · change z 0 (ones 6) true (ones (2*k) ++ [true,false,true]) =
      z 0 (true :: (pairs01 0 ++ ones 5)) true
        (true :: (pairs01 0 ++ ones (2*k) ++ [false,true]))
    rw [show ones 6 = true :: ones 5 by rfl]
    have hr (n : Nat) : ones n ++ [true,false,true] =
        true :: (ones n ++ [false,true]) := by
      induction n with
      | zero => rfl
      | succ n ih =>
          change true :: (ones n ++ [true,false,true]) =
            true :: true :: (ones n ++ [false,true])
          rw [ih]
    rw [hr (2*k)]
    rfl
  · omega

/-- Signed source continuation of every low3 intermediate configuration. -/
theorem stage3_to_junc_delta (v : Nat) :
    runWithDelta (12*v+48) (stage3 v) =
      some (junc 0 0 (4*v+10), -((4*v+8 : Nat) : Int)) := by
  have hc := stage3_to_C0_delta v
  have hj : runWithDelta (2*(2*v+5)+22)
      (z 2 (true::false::ones (4*v+14)) false []) =
      some (junc 0 0 (4*v+10), -((4*v+12 : Nat) : Int)) := by
    have hw : 2*(2*v+5)+4=4*v+14 := by omega
    have hw2 : 2*(2*v+5)=4*v+10 := by omega
    have hw3 : 2*(2*v+5)+2=4*v+12 := by omega
    simpa only [hw,hw2,hw3] using c0_to_junc0_delta (2*v+5)
  have hfull := compose_delta (8*v+16) (2*(2*v+5)+22)
      (stage3 v) (z 2 (true::false::ones (4*v+14)) false [])
      (junc 0 0 (4*v+10)) 4 (-((4*v+12 : Nat) : Int)) hc hj
  have ht : (8*v+16)+(2*(2*v+5)+22) = 12*v+48 := by omega
  have hd : 4+-((4*v+12 : Nat) : Int) = -((4*v+8 : Nat) : Int) := by omega
  simpa only [ht,hd] using hfull

#print axioms af_pairs_delta
#print axioms ar_pairs_delta
#print axioms stage3_to_C0_delta
#print axioms c0_to_junc0_delta
#print axioms stage3_to_junc_delta
end BB429Low3Delta
