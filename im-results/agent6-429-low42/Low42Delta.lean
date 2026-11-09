import Low3Delta
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low42
open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429Low3Delta

/-- Whole source zipper after j actual bubbles from the prepared
    original J(j+2k+1, 2j) tape. -/
def stage42 (j k : Nat) : Zipper :=
  z 0 (ones (4*j) ++ tens (2*k+1) ++ ones 6) true [true,false,true]

private theorem ones_add (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  simp [ones]

private theorem tens_snoc (n : Nat) :
    tens n ++ [true,false] = tens (n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true::false::(tens n ++ [true,false]) =
      true::false::tens (n+1)
    rw [ih]

private theorem tens_to_pairs (n : Nat) :
    tens n ++ ones 6 = true :: (pairs01 n ++ ones 5) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change true :: false :: (tens n ++ ones 6) =
      true :: false :: true :: (pairs01 n ++ ones 5)
    rw [ih]

private theorem af_tail (l r : List Bool) :
  runWithDelta 2 (z 0 (true::false::l) true r) =
    some (z 0 l false (true::false::r), -2) := by
  rfl

private theorem ar_tail (l : List Bool) :
  runWithDelta 2 (z 0 l false [true]) =
    some (z 0 (true::true::l) false [], 2) := by
  rfl

private theorem a0_to_c0 (l : List Bool) :
  runWithDelta 2 (z 0 l false []) =
    some (z 2 (true::true::l) false [], 2) := by
  rfl

private theorem firstC_A_three (l : List Bool) :
  runWithDelta 3 (z 2 (true::l) false []) =
    some (z 0 l true [false,true], -1) := by
  rfl

private theorem a_e_five (k : Nat) (suffix : List Bool) :
  runWithDelta 5 (z 0 (pairs01 (2*k+2) ++ ones 5) true suffix) =
    some (e1After (2*k+1) (ones 2 ++ suffix), -3) := by
  cases k with
  | zero => rfl
  | succ k =>
    simp only [show 2*(k+1)+2 = 2*k+4 by omega,
      show 2*(k+1)+1 = (2*k+2)+1 by omega]
    rfl

private theorem c1_a_four (l r : List Bool) :
  runWithDelta 4 (z 2 l true (ones 2 ++ r)) =
    some (z 0 l false (true::false::r), 0) := by
  rfl

private theorem a_c_four (l : List Bool) :
  runWithDelta 4 (z 0 l false [false,true]) =
    some (z 2 (true::false::true::true::l) false [], 4) := by
  rfl

private theorem compose (m n : Nat) (a b c : Zipper) (d e : Int)
    (h1 : runWithDelta m a = some (b,d))
    (h2 : runWithDelta n b = some (c,e)) :
    runWithDelta (m+n) a = some (c,d+e) := by
  rw [runWithDelta_add,h1]
  simp only [Option.bind_some]
  rw [h2]
  rfl

/-- First source C/0 checkpoint, uniformly in both parameters. -/
theorem to_firstC (j k : Nat) :
  runWithDelta (8*j+10) (stage42 j k) =
    some (z 2 (ones (4*j+8) ++ tens (2*k) ++ ones 6) false [], 6) := by
  have hAF : runWithDelta (4*j) (stage42 j k) =
      some (z 0 (tens (2*k+1) ++ ones 6) true
        (tens (2*j) ++ [true,false,true]), -((4*j:Nat):Int)) := by
    simpa [stage42,List.append_assoc,
      show 2*(2*j)=4*j by omega] using
      (af_pairs_delta (2*j) (tens (2*k+1) ++ ones 6) [true,false,true])
  have h2 : runWithDelta 2
      (z 0 (tens (2*k+1) ++ ones 6) true
        (tens (2*j) ++ [true,false,true])) =
      some (z 0 (tens (2*k) ++ ones 6) false
        (tens (2*j+1) ++ [true,false,true]),-2) := by
    change runWithDelta 2 (z 0 (true::false::(tens (2*k) ++ ones 6)) true
      (tens (2*j) ++ [true,false,true])) =
      some (z 0 (tens (2*k) ++ ones 6) false
        (true::false::(tens (2*j) ++ [true,false,true])),-2)
    exact af_tail _ _
  have hAR : runWithDelta (4*j+4)
      (z 0 (tens (2*k) ++ ones 6) false
        (tens (2*j+1) ++ [true,false,true])) =
      some (z 0 (ones (4*j+4) ++ (tens (2*k) ++ ones 6)) false [true],
        ((4*j+4:Nat):Int)) := by
    have hw : tens (2*j+1) ++ [true,false,true] =
        tens (2*j+2) ++ [true] := by
      calc
        tens (2*j+1) ++ [true,false,true] =
            (tens (2*j+1) ++ [true,false]) ++ [true] := by
              simp [List.append_assoc]
        _ = tens ((2*j+1)+1) ++ [true] := by rw [tens_snoc]
        _ = tens (2*j+2) ++ [true] := by congr 1
    rw [hw]
    simpa only [show 2*(2*j+2)=4*j+4 by omega] using
      (ar_pairs_delta (2*j+2) (tens (2*k) ++ ones 6) [true])
  have h4 : runWithDelta 4
      (z 0 (ones (4*j+4) ++ (tens (2*k) ++ ones 6)) false [true]) =
      some (z 2 (ones (4*j+8) ++ tens (2*k) ++ ones 6) false [],4) := by
    have hA := ar_tail (ones (4*j+4) ++ (tens (2*k) ++ ones 6))
    have hC := a0_to_c0
      (true::true::(ones (4*j+4) ++ (tens (2*k) ++ ones 6)))
    have hh := compose 2 2 _ _ _ 2 2 hA hC
    have hw : true::true::true::true::
        (ones (4*j+4) ++ (tens (2*k) ++ ones 6)) =
        ones (4*j+8) ++ tens (2*k) ++ ones 6 := by
      calc
        true::true::true::true::
            (ones (4*j+4) ++ (tens (2*k) ++ ones 6)) =
            (ones 4 ++ ones (4*j+4)) ++ (tens (2*k) ++ ones 6) := by rfl
        _ = ones (4+(4*j+4)) ++ (tens (2*k) ++ ones 6) := by
          rw [← ones_add]
        _ = ones (4*j+8) ++ tens (2*k) ++ ones 6 := by
          rw [show 4+(4*j+4)=4*j+8 by omega]
          simp [List.append_assoc]
    simpa [hw] using hh
  have htail := compose (4*j+4) 4 _ _ _ ((4*j+4:Nat):Int) 4 hAR h4
  have h212 := compose 2 ((4*j+4)+4) _ _ _
    (-2) (((4*j+4:Nat):Int)+4) h2 htail
  have hall := compose (4*j) (2+((4*j+4)+4)) _ _ _
    (-((4*j:Nat):Int)) (-2+(((4*j+4:Nat):Int)+4)) hAF h212
  have ht : (4*j)+(2+((4*j+4)+4))=8*j+10 := by omega
  have hd : -((4*j:Nat):Int)+(-2+(((4*j+4:Nat):Int)+4))=6 := by omega
  simpa only [ht,hd] using hall

private theorem ones_snoc (n : Nat) :
    ones n ++ [true] = ones (n+1) := by
  simp [ones, ← List.replicate_append_replicate]

/-- First C/0 returns to an A/1 boundary with an even 01-stack. -/
theorem firstC_to_A (j k : Nat) :
  runWithDelta (4*j+11)
    (z 2 (ones (4*j+8) ++ tens (2*k) ++ ones 6) false []) =
    some (z 0 (pairs01 (2*k) ++ ones 5) true
      (tens (2*j+4) ++ [false,true]), -((4*j+9:Nat):Int)) := by
  have hw : ones (4*j+8) ++ tens (2*k) ++ ones 6 =
      true :: (ones (4*j+7) ++ (tens (2*k) ++ ones 6)) := by
    calc
      ones (4*j+8) ++ tens (2*k) ++ ones 6 =
          (ones 1 ++ ones (4*j+7)) ++ (tens (2*k) ++ ones 6) := by
            rw [show 4*j+8=1+(4*j+7) by omega,ones_add]
            simp [List.append_assoc]
      _ = true :: (ones (4*j+7) ++ (tens (2*k) ++ ones 6)) := by rfl
  have h3 : runWithDelta 3
      (z 2 (ones (4*j+8) ++ tens (2*k) ++ ones 6) false []) =
      some (z 0 (ones (4*j+7) ++ (tens (2*k) ++ ones 6)) true
        [false,true], -1) := by
    rw [hw]
    exact firstC_A_three _
  have hleft : ones (4*j+7) ++ (tens (2*k) ++ ones 6) =
      ones (4*j+8) ++ (pairs01 (2*k) ++ ones 5) := by
    rw [tens_to_pairs]
    calc
      ones (4*j+7) ++ (true::(pairs01 (2*k) ++ ones 5)) =
          (ones (4*j+7) ++ [true]) ++ (pairs01 (2*k) ++ ones 5) := by
            simp [List.append_assoc]
      _ = ones ((4*j+7)+1) ++ (pairs01 (2*k) ++ ones 5) := by
        rw [ones_snoc]
      _ = ones (4*j+8) ++ (pairs01 (2*k) ++ ones 5) := by congr 1
  have hAF : runWithDelta (4*j+8)
      (z 0 (ones (4*j+7) ++ (tens (2*k) ++ ones 6)) true [false,true]) =
      some (z 0 (pairs01 (2*k) ++ ones 5) true
        (tens (2*j+4) ++ [false,true]), -((4*j+8:Nat):Int)) := by
    rw [hleft]
    simpa only [show 2*(2*j+4)=4*j+8 by omega] using
      (af_pairs_delta (2*j+4) (pairs01 (2*k) ++ ones 5) [false,true])
  have hc := compose 3 (4*j+8) _ _ _ (-1) (-((4*j+8:Nat):Int)) h3 hAF
  have ht : 3+(4*j+8)=4*j+11 := by omega
  have hd : (-1:Int)+(-((4*j+8:Nat):Int)) = -((4*j+9:Nat):Int) := by omega
  simpa only [ht,hd] using hc

private theorem odd_time (m : Nat) :
    crossTime (2*m+1) = 14*m+15 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2*(m+1)+1=(2*m+1)+2 by omega,crossTime,ih]
    omega

private theorem odd_left (m : Nat) :
    finalLeft (2*m+1) = ones (4*m+8) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [show 2*(m+1)+1=(2*m+1)+2 by omega,finalLeft,ih]
    rw [show 4*(m+1)+8=4+(4*m+8) by omega]
    rw [ones_add 4 (4*m+8)]

private theorem c1_to_secondC (j m : Nat) :
  runWithDelta (4*j+18)
    (z 2 (ones (4*m+8)) true
      (ones 2 ++ (tens (2*j+4) ++ [false,true]))) =
    some (z 2 (true::false::ones (4*j+4*m+20)) false [],
      ((4*j+14:Nat):Int)) := by
  have h4 := c1_a_four (ones (4*m+8))
    (tens (2*j+4) ++ [false,true])
  have hAR : runWithDelta (4*j+10)
      (z 0 (ones (4*m+8)) false
        (true::false::(tens (2*j+4) ++ [false,true]))) =
      some (z 0 (ones (4*j+10) ++ ones (4*m+8)) false [false,true],
        ((4*j+10:Nat):Int)) := by
    change runWithDelta (4*j+10)
      (z 0 (ones (4*m+8)) false
        (tens ((2*j+4)+1) ++ [false,true])) = _
    simpa only [show 2*((2*j+4)+1)=4*j+10 by omega] using
      (ar_pairs_delta ((2*j+4)+1) (ones (4*m+8)) [false,true])
  have htail : runWithDelta 4
      (z 0 (ones (4*j+10) ++ ones (4*m+8)) false [false,true]) =
      some (z 2 (true::false::ones (4*j+4*m+20)) false [],4) := by
    have hw : true::true::(ones (4*j+10) ++ ones (4*m+8)) =
        ones (4*j+4*m+20) := by
      calc
        true::true::(ones (4*j+10) ++ ones (4*m+8)) =
            (ones 2 ++ ones (4*j+10)) ++ ones (4*m+8) := by rfl
        _ = ones (2+(4*j+10)+(4*m+8)) := by
          rw [← ones_add,← ones_add]
        _ = ones (4*j+4*m+20) := by congr 1; omega
    simpa only [hw] using
      a_c_four (ones (4*j+10) ++ ones (4*m+8))
  have htailFull := compose (4*j+10) 4 _ _ _
    ((4*j+10:Nat):Int) 4 hAR htail
  have hfull := compose 4 ((4*j+10)+4) _ _ _
    0 (((4*j+10:Nat):Int)+4) h4 htailFull
  have ht : 4+((4*j+10)+4)=4*j+18 := by omega
  have hd : (0:Int)+(((4*j+10:Nat):Int)+4)=((4*j+14:Nat):Int) := by omega
  simpa only [ht,hd] using hfull

/-- From the first C/0 checkpoint, k=m+1 reaches a second C/0
    after an exact 01-stack crossing and an E/1 return. -/
theorem firstC_to_secondC (j m : Nat) :
  runWithDelta (8*j+14*m+49)
    (z 2 (ones (4*j+8) ++ tens (2*(m+1)) ++ ones 6) false []) =
    some (z 2 (true::false::ones (4*j+4*m+20)) false [], 3) := by
  let suffix : List Bool := tens (2*j+4) ++ [false,true]
  have hCA := firstC_to_A j (m+1)
  have h5 : runWithDelta 5
      (z 0 (pairs01 (2*(m+1)) ++ ones 5) true suffix) =
      some (e1After (2*m+1) (ones 2 ++ suffix), -3) := by
    simpa only [show 2*(m+1)=2*m+2 by omega] using
      a_e_five m suffix
  have hCross : runWithDelta (14*m+15)
      (e1After (2*m+1) (ones 2 ++ suffix)) =
      some (z 2 (ones (4*m+8)) true (ones 2 ++ suffix), 1) := by
    simpa only [odd_time,odd_left] using
      (e1_cross_delta (2*m+1) (ones 2 ++ suffix))
  have hC := c1_to_secondC j m
  have h345 := compose 5 (14*m+15) _ _ _ (-3) 1 h5 hCross
  have h3456 := compose (5+(14*m+15)) (4*j+18) _ _ _
    (-3+1) ((4*j+14:Nat):Int) h345 hC
  have h := compose (4*j+11) ((5+(14*m+15))+(4*j+18)) _ _ _
    (-((4*j+9:Nat):Int))
    ((-3+1)+((4*j+14:Nat):Int)) hCA h3456
  have ht : (4*j+11)+((5+(14*m+15))+(4*j+18))=
    8*j+14*m+49 := by omega
  have hd : -((4*j+9:Nat):Int)+((-3+1)+((4*j+14:Nat):Int))=3 := by
    omega
  simpa only [ht,hd] using h

/-- Entire two-parameter source transition for every m,j: the
    deficit r=4(m+1)+2 family. Every intermediate step is defined.
    These are prepared inputs, without a blank-root claim. -/
theorem low42_source (j m : Nat) :
  runWithDelta (20*j+18*(m+1)+79) (stage42 j (m+1)) =
    some (junc 0 0 (4*j+4*(m+1)+12),
      -((4*j+4*(m+1)+5:Nat):Int)) := by
  have hfirst := to_firstC j (m+1)
  have hsecond := firstC_to_secondC j m
  have hlast : runWithDelta (2*(2*j+2*m+8)+22)
      (z 2 (true::false::ones (4*j+4*m+20)) false []) =
      some (junc 0 0 (4*j+4*(m+1)+12),
        -((2*(2*j+2*m+8)+2:Nat):Int)) := by
    have hw : 2*(2*j+2*m+8)+4=4*j+4*m+20 := by omega
    have htarget : 2*(2*j+2*m+8)=4*j+4*(m+1)+12 := by omega
    have hextra : (4*j+4*(m+1)+12)+4=4*j+4*m+20 := by omega
    simpa only [htarget,hextra] using
      c0_to_junc0_delta (2*j+2*m+8)
  have h12 := compose (8*j+10) (8*j+14*m+49)
    _ _ _ 6 3 hfirst hsecond
  have h123 := compose ((8*j+10)+(8*j+14*m+49))
    (2*(2*j+2*m+8)+22) _ _ _ (6+3)
    (-((2*(2*j+2*m+8)+2:Nat):Int)) h12 hlast
  have ht : ((8*j+10)+(8*j+14*m+49))+
      (2*(2*j+2*m+8)+22)=20*j+18*(m+1)+79 := by omega
  have he : ((6+3):Int) + -((2*(2*j+2*m+8)+2:Nat):Int) =
      -((4*j+4*(m+1)+5:Nat):Int) := by omega
  simpa only [ht,he] using h123

#print axioms to_firstC
#print axioms firstC_to_A
#print axioms firstC_to_secondC
#print axioms low42_source
end BB429Low42
