import BB429FinishScanEDelta
import BB429JuncHeadExcursion
import BB429PhysicalBridge
import BB429SourceE1Return
import BB429SourceE1Delta
import Low3Delta
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 65536

namespace BB429LowEven4k

open BB6Coverage BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429Low3Delta BB429PhysicalFrontier BB429PhysicalBridge
open BB429DeltaPhysicalBridge

private theorem compose_delta
    (m n : Nat) (a b c : Zipper) (d e : Int)
    (h1 : runWithDelta m a = some (b, d))
    (h2 : runWithDelta n b = some (c, e)) :
    runWithDelta (m+n) a = some (c, d+e) := by
  rw [runWithDelta_add, h1]
  simp only [Option.bind_some]
  rw [h2]
  rfl


private theorem shift_A01_tail_delta (n : Nat) (hn : 1 ≤ n) (left : List Bool) :
    runWithDelta (2*n) (z 0 left false (true :: pairs01 n)) =
      some (z 0 (ones (2*n) ++ left) false [true], ((2*n : Nat) : Int)) := by
  induction n generalizing left with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          simpa [pairs01, ones] using
            (shift_A01_pair_delta left [false,true])
      | succ n =>
          have hpair :
              runWithDelta 2
                (z 0 left false (true :: (false :: true :: pairs01 (n+1)))) =
              some (z 0 (true :: true :: left) false (true :: pairs01 (n+1)), 2) := by
            simpa [pairs01] using
              (shift_A01_pair_delta left (false :: true :: pairs01 (n+1)))
          have htail := ih (by omega) (true :: true :: left)
          have htime : 2*(n+2) = 2 + 2*(n+1) := by omega
          rw [htime, runWithDelta_add]
          have hpair' :
              runWithDelta 2 (z 0 left false (true :: pairs01 (n+2))) =
                some (z 0 (true :: true :: left) false (true :: pairs01 (n+1)), 2) := by
            simpa only [pairs01] using hpair
          rw [hpair']
          simp only [Option.bind_some]
          rw [htail]
          simp only [Option.map_some]
          have hleft : ones (2*(n+1)) ++ [true,true] = ones (2*(n+2)) := by
            calc
              ones (2*(n+1)) ++ [true,true] =
                  ones (2*(n+1)) ++ ones 2 := by simp [ones]
              _ = ones (2*(n+1)+2) := by rw [← BB429SourceE1Return.ones_add]
              _ = ones (2*(n+2)) := by congr 1 <;> omega
          have hleft' : ones (2*(n+1)) ++ (true :: true :: left) =
              ones (2+2*(n+1)) ++ left := by
            calc
              ones (2*(n+1)) ++ (true :: true :: left) =
                  (ones (2*(n+1)) ++ [true,true]) ++ left := by
                    rw [show true :: true :: left = [true,true] ++ left by rfl,
                      ← List.append_assoc]
              _ = ones (2+2*(n+1)) ++ left := by
                rw [hleft]
                rw [show 2*(n+2) = 2+2*(n+1) by omega]
          rw [hleft']
          simp [Int.natCast_add, Int.natCast_mul]

private theorem juncPos_w0_exit_delta (u v : Nat) :
    runWithDelta (2*v+6) (junc (u+1) v 0) =
      some (z 0 (ones (2*v+5) ++ pairs01 u ++ ones 5) false [true],
        ((2*v+2 : Nat) : Int)) := by
  have hprep := juncPos_prep4_delta u v 0
  have htail := shift_A01_tail_delta (v+1) (by omega)
    (true :: true :: true :: (pairs01 u ++ ones 5))
  have htime : 2*v+6 = 4 + 2*(v+1) := by omega
  rw [htime, runWithDelta_add, hprep]
  simp only [Option.bind_some]
  have hright : pairs01 v ++ ones 0 ++ [false,true] = pairs01 (v+1) := by
    simpa [ones] using pairs01_succ_append v
  have hinput :
      z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones 0 ++ [false,true])) =
      z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: pairs01 (v+1)) := by
    exact congrArg (fun r : List Bool =>
      z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false (true :: r)) hright
  rw [hinput, htail]
  simp only [Option.map_some]
  have hleft : ones (2*(v+1)) ++ [true,true,true] = ones (2*v+5) := by
    calc
      ones (2*(v+1)) ++ [true,true,true] =
          ones (2*(v+1)) ++ ones 3 := by simp [ones]
      _ = ones (2*(v+1)+3) := by rw [← BB429SourceE1Return.ones_add]
      _ = ones (2*v+5) := by congr 1 <;> omega
  have hleft' :
      ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 u ++ ones 5)) =
        ones (2*v+5) ++ pairs01 u ++ ones 5 := by
    calc
      ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 u ++ ones 5)) =
          (ones (2*(v+1)) ++ [true,true,true]) ++ (pairs01 u ++ ones 5) := by
            rw [show true :: true :: true :: (pairs01 u ++ ones 5) =
              [true,true,true] ++ (pairs01 u ++ ones 5) by rfl,
              ← List.append_assoc]
      _ = ones (2*v+5) ++ pairs01 u ++ ones 5 := by
        rw [hleft, List.append_assoc]
  rw [hleft']
  simp [Int.natCast_add, Int.natCast_mul]
  omega

private theorem E1_sweep_prefix_delta (n : Nat) (left suffix : List Bool) :
    runWithDelta n (z 4 (ones n ++ left) true suffix) =
      some (z 4 left true (ones n ++ suffix), -((n : Nat) : Int)) := by
  induction n generalizing left suffix with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n+1 = 1+n by omega, runWithDelta_add]
      have hleft : ones (1+n) ++ left = true :: (ones n ++ left) := by
        rw [BB429SourceE1Return.ones_add 1 n]
        simp [ones]
      have hstep :
          runWithDelta 1 (z 4 (ones (1+n) ++ left) true suffix) =
            some (z 4 (ones n ++ left) true (true :: suffix), -1) := by
        rw [hleft]
        rfl
      rw [hstep]
      simp only [Option.bind_some]
      rw [ih]
      simp only [Option.map_some]
      have hones : ones n ++ [true] = ones (n+1) := by
        simpa [ones] using (BB429SourceE1Return.ones_add n 1).symm
      have hright : ones n ++ (true :: suffix) = ones (n+1) ++ suffix := by
        calc
          ones n ++ (true :: suffix) = ones n ++ ([true] ++ suffix) := rfl
          _ = (ones n ++ [true]) ++ suffix := by rw [← List.append_assoc]
          _ = ones (n+1) ++ suffix := by rw [hones]
      rw [hright, show n+1 = 1+n by omega]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · trivial
      · omega

private theorem pairs01_snoc (n : Nat) :
    pairs01 (n+1) = pairs01 n ++ [false, true] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false :: true :: pairs01 (n+1) =
        (false :: true :: pairs01 n) ++ [false, true]
      rw [ih]
      rfl

private theorem pairs01_to_tens (n : Nat) :
    pairs01 n ++ [false, false, true] =
      false :: (tens n ++ [false, true]) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change false :: true :: (pairs01 n ++ [false, false, true]) =
        false :: true :: false :: (tens n ++ [false, true])
      rw [ih]

private theorem first_suffix_rewrite (v : Nat) :
    ones 3 ++ pairs01 (v+3) ++ [false, false, true] =
      ones 2 ++ tens (v+4) ++ [false, true] := by
  calc
    ones 3 ++ pairs01 (v+3) ++ [false, false, true] =
        ones 3 ++ (false :: (tens (v+3) ++ [false, true])) := by
          rw [List.append_assoc, pairs01_to_tens]
    _ = ones 2 ++ tens (v+4) ++ [false, true] := by
          rw [show v+4 = Nat.succ (v+3) by omega]
          rfl

private theorem finalLeft_lowEven (k : Nat) (hk : 1 ≤ k) :
    finalLeft (2*k-2) = ones (4*k-3) ++ pairs01 2 ++ ones 5 := by
  have hi : 2*k-2 = 2*(k-1) := by omega
  rw [hi, finalLeft_even (k-1)]
  have hn : 4*(k-1)+1 = 4*k-3 := by omega
  rw [hn]
  rfl

private theorem firstC_A_three (l : List Bool) :
    runWithDelta 3 (z 2 (true :: l) false []) =
      some (z 0 l true [false, true], -1) := by
  rfl

private theorem ar_tail (l : List Bool) :
    runWithDelta 2 (z 0 l false [true]) =
      some (z 0 (true :: true :: l) false [], 2) := by
  rfl

private theorem a0_to_c0 (l : List Bool) :
    runWithDelta 2 (z 0 (true :: true :: l) false []) =
      some (z 2 (true :: true :: true :: true :: l) false [], 2) := by
  rfl

private theorem c1_a_four (l r : List Bool) :
    runWithDelta 4 (z 2 l true (ones 2 ++ r)) =
      some (z 0 l false (true :: false :: r), 0) := by
  rfl

private theorem a_c_four (l : List Bool) :
    runWithDelta 4 (z 0 l false [false, true]) =
      some (z 2 (true :: false :: true :: true :: l) false [], 4) := by
  rfl

private theorem c0_to_e1_six (n : Nat) (tail : List Bool) :
    runWithDelta 6 (z 2 (true :: false :: (ones n ++ tail)) false []) =
      some (z 4 (ones n ++ tail) true [true, false, true], -2) := by
  rfl

private theorem a_e_four (k v : Nat) (hk : 1 ≤ k) :
    runWithDelta 4
      (z 0 (pairs01 (2*k-1) ++ ones 5) true
        (tens (v+4) ++ [false, true])) =
      some (sourceScanE (2*k-2)
        (ones 3 ++ pairs01 (v+3) ++ [false, false, true]), -2) := by
  have hleft : 2*k-1 = (2*k-2)+1 := by omega
  have hv4 : v+4 = 4+v := by omega
  have hv3 : v+3 = 3+v := by omega
  rw [hleft, pairs01_snoc, hv4, hv3]
  simpa [sourceScanE, first_suffix_rewrite, List.append_assoc]

private theorem firstC_to_secondC
    (k v : Nat) :
    runWithDelta (2*v+18)
      (z 2 (ones (4*k-3) ++ pairs01 2 ++ ones 5) true
        (ones 2 ++ (tens (v+4) ++ [false, true]))) =
      some (z 2
        (true :: false :: ones (2*v+4*k+9) ++ pairs01 2 ++ ones 5)
        false [], ((2*v+14 : Nat) : Int)) := by
  let l := ones (4*k-3) ++ pairs01 2 ++ ones 5
  have h1 :
      runWithDelta 4 (z 2 l true
        (ones 2 ++ (tens (v+4) ++ [false, true]))) =
        some (z 0 l false (tens (v+5) ++ [false, true]), 0) := by
    have ht : tens (v+5) = true :: false :: tens (v+4) := by
      rw [show v+5 = Nat.succ (v+4) by omega]
      rfl
    simpa [ht] using c1_a_four l (tens (v+4) ++ [false, true])
  have h2 :
      runWithDelta (2*v+10)
        (z 0 l false (tens (v+5) ++ [false, true])) =
        some (z 0 (ones (2*v+10) ++ l) false [false, true], ((2*v+10 : Nat) : Int)) := by
    simpa [show 2*(v+5) = 2*v+10 by omega] using
      (ar_pairs_delta (v+5) l [false, true])
  have h3 :
      runWithDelta 4 (z 0 (ones (2*v+10) ++ l) false [false, true]) =
        some (z 2
          (true :: false :: true :: true :: (ones (2*v+10) ++ l))
          false [], 4) := by
    exact a_c_four (ones (2*v+10) ++ l)
  have h12 := compose_delta 4 (2*v+10) (z 2 l true
      (ones 2 ++ (tens (v+4) ++ [false, true])))
      (z 0 l false (tens (v+5) ++ [false, true]))
      (z 0 (ones (2*v+10) ++ l) false [false, true])
      0 (2*v+10) h1 h2
  have htotal := compose_delta (4+(2*v+10)) 4
      (z 2 l true (ones 2 ++ (tens (v+4) ++ [false, true])))
      (z 0 (ones (2*v+10) ++ l) false [false, true])
      (z 2 (true :: false :: true :: true :: (ones (2*v+10) ++ l))
        false [])
      ((2*v+10 : Nat) : Int) 4 h12 h3
  have hleft :
      true :: false :: true :: true :: (ones (2*v+10) ++ l) =
        true :: false :: ones (2*v+4*k+9) ++ pairs01 2 ++ ones 5 := by
    dsimp [l]
    change [true, false] ++ (ones 2 ++ ones (2*v+10) ++ ones (4*k-3)) ++ pairs01 2 ++ ones 5 =
      [true, false] ++ ones (2*v+4*k+9) ++ pairs01 2 ++ ones 5
    apply congrArg (fun xs : List Bool => [true, false] ++ xs ++ pairs01 2 ++ ones 5)
    calc
      ones 2 ++ ones (2*v+10) ++ ones (4*k-3) =
          ones (2+(2*v+10)) ++ ones (4*k-3) := by
            rw [← BB429SourceE1Return.ones_add 2 (2*v+10)]
      _ = ones (2+(2*v+10)+(4*k-3)) := by
            rw [← BB429SourceE1Return.ones_add (2+(2*v+10)) (4*k-3)]
      _ = ones (2*v+4*k+9) := by congr 1 <;> omega
  have ht : (4+(2*v+10))+4 = 2*v+18 := by omega
  simpa [ht, hleft] using htotal

def firstC (k v : Nat) : Zipper :=
  z 2 (ones (2*v+9) ++ pairs01 (2*k-1) ++ ones 5) false []

def firstScanE (k v : Nat) : Zipper :=
  sourceScanE (2*k-2)
    (ones 3 ++ pairs01 (v+3) ++ [false, false, true])

def revisitC1 (k v : Nat) : Zipper :=
  z 2 (ones (4*k-3) ++ pairs01 2 ++ ones 5) true
    (ones 2 ++ tens (v+4) ++ [false, true])

def secondC (k v : Nat) : Zipper :=
  z 2 (true :: false :: ones (2*v+4*k+9) ++ pairs01 2 ++ ones 5)
    false []

def secondScanE (k v : Nat) : Zipper :=
  sourceScanE 2 (sourceSuffix (v+2*k+2))

/-- Junc(2k,v,0) reaches the first C/0 configuration in 2v+10 steps. -/
theorem junc_to_firstC (k v : Nat) (hk : 1 ≤ k) :
    runWithDelta (2*v+10) (junc (2*k) v 0) =
      some (firstC k v, ((2*v+6 : Nat) : Int)) := by
  have hExit := juncPos_w0_exit_delta (2*k-1) v
  have hu : (2*k-1)+1 = 2*k := by omega
  have hExit' :
      runWithDelta (2*v+6) (junc (2*k) v 0) =
        some (z 0 (ones (2*v+5) ++ pairs01 (2*k-1) ++ ones 5)
          false [true], ((2*v+2 : Nat) : Int)) := by
    simpa [hu] using hExit
  let l := ones (2*v+5) ++ pairs01 (2*k-1) ++ ones 5
  have h1 := ar_tail l
  have h2 := a0_to_c0 l
  have h12 := compose_delta 2 2 (z 0 l false [true])
      (z 0 (true :: true :: l) false [])
      (z 2 (true :: true :: true :: true :: l) false [])
      2 2 h1 h2
  have htotal := compose_delta (2*v+6) 4
      (junc (2*k) v 0) (z 0 l false [true])
      (z 2 (true :: true :: true :: true :: l) false [])
      (2*v+2) 4 hExit' h12
  have hleft :
      true :: true :: true :: true :: l =
        ones (2*v+9) ++ pairs01 (2*k-1) ++ ones 5 := by
    dsimp [l]
    calc
      true :: true :: true :: true ::
          (ones (2*v+5) ++ pairs01 (2*k-1) ++ ones 5) =
        (ones 4 ++ ones (2*v+5)) ++ pairs01 (2*k-1) ++ ones 5 := by rfl
      _ = ones (4+(2*v+5)) ++ pairs01 (2*k-1) ++ ones 5 := by
        rw [← BB429SourceE1Return.ones_add]
      _ = ones (2*v+9) ++ pairs01 (2*k-1) ++ ones 5 := by
        congr 1 <;> omega
  have ht : (2*v+6)+4 = 2*v+10 := by omega
  simpa [firstC, l, ht, hleft] using htotal

#print axioms junc_to_firstC

/-- First C/0-to-E/1 leg, preserving the arbitrary alternating left tail. -/
theorem firstC_to_sourceScanE (k v : Nat) (hk : 1 ≤ k) :
    runWithDelta (2*v+15) (firstC k v) =
      some (firstScanE k v, -(2*v+11 : Int)) := by
  let tail := pairs01 (2*k-1) ++ ones 5
  have hsplit : ones (2*v+9) = true :: ones (2*v+8) := by
    rw [show 2*v+9 = 1+(2*v+8) by omega,
      BB429SourceE1Return.ones_add 1 (2*v+8)]
    simp [ones]
  have h1 :
      runWithDelta 3 (firstC k v) =
        some (z 0 (ones (2*v+8) ++ tail) true [false, true], -1) := by
    rw [firstC, hsplit]
    simpa [tail, List.append_assoc] using
      (firstC_A_three (ones (2*v+8) ++ tail))
  have h2 :
      runWithDelta (2*v+8)
        (z 0 (ones (2*v+8) ++ tail) true [false, true]) =
        some (z 0 tail true (tens (v+4) ++ [false, true]),
          -(2*v+8 : Int)) := by
    simpa [show 2*(v+4) = 2*v+8 by omega] using
      (af_pairs_delta (v+4) tail [false, true])
  have h3 := a_e_four k v hk
  have h12 := compose_delta 3 (2*v+8) (firstC k v)
      (z 0 (ones (2*v+8) ++ tail) true [false, true])
      (z 0 tail true (tens (v+4) ++ [false, true]))
      (-1) (-(2*v+8 : Int)) h1 h2
  have htotal := compose_delta (3+(2*v+8)) 4 (firstC k v)
      (z 0 tail true (tens (v+4) ++ [false, true]))
      (firstScanE k v) (-1-(2*v+8 : Int)) (-2) h12 h3
  have ht : (3+(2*v+8))+4 = 2*v+15 := by omega
  have hd : (-1 : Int) - (2*v+8 : Int) + (-2) = -(2*v+11 : Int) := by omega
  simpa [firstScanE, tail, ht, hd] using htotal

#print axioms firstC_to_sourceScanE

/-- The E/1 revisit returns to C/1 with the even final-left pattern. -/
theorem sourceScanE_to_secondC (k v : Nat) (hk : 1 ≤ k) :
    runWithDelta (14*k+28+2*v+18) (firstScanE k v) =
      some (secondC k v, ((2*v+14 : Nat) : Int)) := by
  have hrev := sourceScanE_e1_revisit_delta (2*k-2)
    (ones 3 ++ pairs01 (v+3) ++ [false, false, true])
  have hleft := finalLeft_lowEven k hk
  have hright := first_suffix_rewrite v
  have htime : crossTime (2*k-2)+1 = 14*k+28 := by
    rw [show 2*k-2 = 2*(k-1) by omega, crossTime_even]
    omega
  have hrev' :
      runWithDelta (14*k+28) (firstScanE k v) =
        some (revisitC1 k v, 0) := by
    simpa [firstScanE, revisitC1, hleft, hright, htime] using hrev
  have hC := firstC_to_secondC k v
  have htotal := compose_delta (14*k+28) (2*v+18)
      (firstScanE k v) (revisitC1 k v) (secondC k v)
      0 (2*v+14) hrev' hC
  have ht : (14*k+28)+(2*v+18) = 14*k+2*v+46 := by omega
  simpa [ht] using htotal

#print axioms sourceScanE_to_secondC

/-- Six-step second C/0-to-E/1 prefix, followed by a tail-preserving E/1 sweep. -/
theorem secondC_to_sourceScanE (k v : Nat) :
    runWithDelta (2*v+4*k+15) (secondC k v) =
      some (secondScanE k v, -(2*v+4*k+11 : Int)) := by
  let n := 2*v+4*k+9
  let tail := pairs01 2 ++ ones 5
  have h1 :
      runWithDelta 6 (secondC k v) =
        some (z 4 (ones n ++ tail) true [true, false, true], -2) := by
    simpa [secondC, n, tail, List.append_assoc] using
      (c0_to_e1_six n tail)
  have h2 := E1_sweep_prefix_delta n tail [true, false, true]
  have hright : ones n ++ [true, false, true] =
      sourceSuffix (v+2*k+2) := by
    have hs : ones n ++ [true] = ones (n+1) := by
      simpa [ones] using (BB429SourceE1Return.ones_add n 1).symm
    have hn : n+1 = 6+2*(v+2*k+2) := by omega
    calc
      ones n ++ [true, false, true] =
          ones n ++ ([true] ++ [false, true]) := by rfl
      _ = (ones n ++ [true]) ++ [false, true] := by
        rw [← List.append_assoc]
      _ = ones (n+1) ++ [false, true] := by rw [hs]
      _ = (ones 6 ++ ones (2*(v+2*k+2))) ++ [false, true] := by
        rw [hn, BB429SourceE1Return.ones_add 6 (2*(v+2*k+2))]
      _ = sourceSuffix (v+2*k+2) := by
        simp [sourceSuffix, List.append_assoc]
  have h2' :
      runWithDelta n (z 4 (ones n ++ tail) true [true, false, true]) =
        some (secondScanE k v, -(n : Int)) := by
    simpa [secondScanE, sourceScanE, tail] using h2
  have htotal := compose_delta 6 n (secondC k v)
      (z 4 (ones n ++ tail) true [true, false, true])
      (secondScanE k v) (-2) (-(n : Int)) h1 h2'
  have ht : 6+n = 2*v+4*k+15 := by omega
  have hd : (-2 : Int) + (-(n : Int)) = -(2*v+4*k+11 : Int) := by omega
  simpa [n, ht, hd] using htotal

#print axioms secondC_to_sourceScanE

/-- The final 175-step sourceScanE continuation closes at Junc(11,0,*). -/
theorem final_sourceScanE (k v : Nat) :
    runWithDelta 175 (secondScanE k v) =
      some (junc 11 0 (2*v+4*k-2), 11) := by
  have h := sourceScanE_finishC_even_after_junc0_delta 1
    (v+2*k+2) (by omega)
  have ht :
      ((crossTime (2*1)+1+(12+2*(2*1))) +
        (juncPosFullTime 2 (2*1+2) + (2*(2*1+6)+27))) = 175 := by
    norm_num [crossTime, juncPosFullTime]
  have htarget :
      junc (2*1+9) 0 (2*(v+2*k+2)-6) =
        junc 11 0 (2*v+4*k-2) := by
    norm_num
    apply congrArg (fun w : Nat => junc 11 0 w)
    by_cases hzero : 2*v+4*k = 0
    · have hv : v = 0 := by omega
      have hk : k = 0 := by omega
      subst v
      subst k
      norm_num
    · have hpos : 2 ≤ 2*v+4*k := by omega
      omega
  simpa [secondScanE, ht, htarget] using h

#print axioms final_sourceScanE

/-- Parameter-uniform exact source suffix from Junc(2k,v,0) to
    Junc(11,0,2v+4k-2), valid for every k>=1 and every v>=0. -/
theorem lowEven4k_suffix_delta (k v : Nat) (hk : 1 ≤ k) :
    runWithDelta (8*v+18*k+261) (junc (2*k) v 0) =
      some (junc 11 0 (2*v+4*k-2), (9-4*k : Int)) := by
  have h1 := junc_to_firstC k v hk
  have h2 := firstC_to_sourceScanE k v hk
  have h3 := sourceScanE_to_secondC k v hk
  have h4 := secondC_to_sourceScanE k v
  have h5 := final_sourceScanE k v
  have h12 := compose_delta (2*v+10) (2*v+15)
      (junc (2*k) v 0) (firstC k v) (firstScanE k v)
      (2*v+6) (-(2*v+11 : Int)) h1 h2
  have h123 := compose_delta (2*v+10+2*v+15) (14*k+28+2*v+18)
      (junc (2*k) v 0) (firstScanE k v) (secondC k v)
      ((2*v+6)+(-(2*v+11 : Int))) (2*v+14) h12 h3
  have h1234 := compose_delta
      (2*v+10+2*v+15+(14*k+28+2*v+18)) (2*v+4*k+15)
      (junc (2*k) v 0) (secondC k v) (secondScanE k v)
      ((2*v+6)+(-(2*v+11 : Int))+(2*v+14))
      (-(2*v+4*k+11 : Int)) h123 h4
  have htotal := compose_delta
      (2*v+10+2*v+15+(14*k+28+2*v+18)+(2*v+4*k+15)) 175
      (junc (2*k) v 0) (secondScanE k v)
      (junc 11 0 (2*v+4*k-2))
      ((2*v+6)+(-(2*v+11 : Int))+(2*v+14)+(-(2*v+4*k+11 : Int)))
      11 h1234 h5
  have ht :
      (2*v+10+2*v+15+(14*k+28+2*v+18)+(2*v+4*k+15))+175 =
        8*v+18*k+261 := by omega
  have hd :
      (2*v+6)+(-(2*v+11 : Int))+(2*v+14)+
        (-(2*v+4*k+11 : Int))+11 = 9-4*k := by omega
  simpa [ht, hd] using htotal

#print axioms lowEven4k_suffix_delta

/-- The complete low-even r=4k prepared return, preceded by N full
    positive-u Junc transitions. Here u=N+2k and the initial right budget
    is 2N. -/
theorem lowEven4k_prepared_return_delta (N k : Nat) (hk : 1 ≤ k) :
    runWithDelta
      (juncPosFullTime N 0 + (16*N+18*k+261))
      (junc (N+2*k) 0 (2*N)) =
      some (junc 11 0 (4*N+4*k-2), (9-2*(N+2*k) : Int)) := by
  have hprefix := juncPos_iter_full_delta N (N+2*k) 0 (2*N)
    (by omega) (by omega)
  have hsuffix := lowEven4k_suffix_delta k (2*N) hk
  have htime :
      juncPosFullTime N 0 + (16*N+18*k+261) =
        juncPosFullTime N 0 + (8*(2*N)+18*k+261) := by omega
  rw [htime, runWithDelta_add, hprefix]
  simp only [Option.bind_some]
  have hmid :
      junc ((N+2*k)-N) (0+2*N) (2*N-2*N) = junc (2*k) (2*N) 0 := by
    congr 1 <;> omega
  rw [hmid, hsuffix]
  simp only [Option.map_some]
  congr 1 <;> omega

#print axioms lowEven4k_prepared_return_delta

/-- Physical lifting of the entire parameterized low-even prepared return. -/
theorem lowEven4k_prepared_return_physical
    (N k : Nat) (hk : 1 ≤ k) (c : Config)
    (hrep : Represents (junc (N+2*k) 0 (2*N)) c) :
    ∃ d : Config,
      BB6Coverage.run target429
        (juncPosFullTime N 0 + (16*N+18*k+261)) c = some d ∧
      Represents (junc 11 0 (4*N+4*k-2)) d ∧
      d.head = c.head + (9-2*(N+2*k) : Int) := by
  obtain ⟨d, hraw, hrepD, hhead⟩ :=
    source_runWithDelta_rep
      (juncPosFullTime N 0 + (16*N+18*k+261))
      (junc (N+2*k) 0 (2*N)) c hrep
      (junc 11 0 (4*N+4*k-2))
      (9-2*(N+2*k) : Int)
      (lowEven4k_prepared_return_delta N k hk)
  exact ⟨d, hraw, hrepD, hhead⟩

#print axioms lowEven4k_prepared_return_physical

#print axioms junc_to_firstC
#print axioms firstC_to_sourceScanE
#print axioms sourceScanE_to_secondC
#print axioms secondC_to_sourceScanE
#print axioms final_sourceScanE
#print axioms lowEven4k_suffix_delta
#print axioms lowEven4k_prepared_return_delta
#print axioms lowEven4k_prepared_return_physical

end BB429LowEven4k
