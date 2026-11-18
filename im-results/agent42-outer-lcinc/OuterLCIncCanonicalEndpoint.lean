import OuterLCIncPostludeSource
import CountedSuffixOutput
import Lean.Elab.Tactic.Omega

/-!
# Canonical endpoint lemmas for the outer LC increment

The exact source run in OuterLCIncPostludeSource ends in a nested frame.
This file begins the pointwise identification of that frame with the
canonical marker-1 S1/S0 target for the authentic m=2,n=1 root branch.
All claims here remain intermediate until the complete module is compiled
and its exported axiom profile is checked.
-/

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8OuterLCInc
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion

/--
At the n=1,m=2 root branch, the outer H-run has valuation zero.  Its
left-facing output at h1 is exactly BinDec(L,0) ++ lh: the marker bridge
preserves the original BinDec(L,1) tail, and the zero-valuation bridge
changes the first d0 block to d1.
-/
theorem outerLCIncSourceT3_leftFacing_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ i : Nat,
      outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0
        (outerLCIncH1 h a 2 - (i:Int)) =
      sideBit (d1pow L ++ lh) i := by
  let T : Int → Bool := (s1Config L 1 2 a 0 b h).tape
  let h0 : Int := h-(3*a:Int)
  let h1 : Int := outerLCIncH1 h a 2
  let T2 : Int → Bool := outerLCIncSourceT2 T h a 2
  have hbin : binDec L 1 = d0 ++ d1pow (L-1) := by
    cases L with
    | zero =>
        omega
    | succ k =>
        have hk : 0 < 2^k := Nat.pow_pos (by decide)
        rw [binDec_odd k 0 (by omega)]
        simp [binDec_zero]
  have htail : binDec L 1 ++ lh =
      d0 ++ (d1pow (L-1) ++ lh) := by
    rw [hbin]
    simp [List.append_assoc]
  have hT2left : ∀ i : Nat,
      T2 (h1-(i:Int)) =
        sideBit (d0 ++ (d1pow (L-1) ++ lh)) i := by
    intro i
    have hp := outer_markerBridge_preserves_source L 1 2 a b h
      (by omega) (h1-(i:Int)) (by
        dsimp [h1,outerLCIncH1]
        omega)
    have hc := outer_s1_counter_cell L 1 2 a b h (by omega) i
    have hcoord : h1-(i:Int) =
        h-((3*a+2+5+i):Int) := by
      dsimp [h1,outerLCIncH1]
      omega
    calc
      T2 (h1-(i:Int)) = T (h1-(i:Int)) := by
        simpa [T2,T,outerLCIncSourceT2,outerLCIncSourceT1,h0] using hp
      _ = sideBit (binDec L 1 ++ lh) i := by
        rw [hcoord]
        simpa [T] using hc
      _ = sideBit (d0 ++ (d1pow (L-1) ++ lh)) i := by
        rw [htail]
  have hT3eq (i : Nat) :
      outerLCIncSourceT3 T h a 2 0 (h1-(i:Int)) =
        afterLIncBridge T2 h1 (h1-(i:Int)) := by
    change lbinDecHRunTape 0 T2 h1 (h1-(i:Int)) = _
    simp [lbinDecHRunTape,sweptLeft,sweptRightB]
  have hword : d1pow L ++ lh =
      d1 ++ (d1pow (L-1) ++ lh) := by
    cases L with
    | zero =>
        omega
    | succ k =>
        simp [d1pow,List.append_assoc]
  have hbit (i : Nat) (hi : 2 ≤ i) :
      sideBit (d0 ++ (d1pow (L-1) ++ lh)) i =
        sideBit (d1 ++ (d1pow (L-1) ++ lh)) i := by
    by_cases hsmall : i < 3
    · have hi2 : i = 2 := by omega
      subst i
      simp [sideBit,d0,d1]
    · have hd0 : ¬ i < d0.length := by
        simp [d0]
        omega
      have hd1 : ¬ i < d1.length := by
        simp [d1]
        omega
      rw [sideBit_append,sideBit_append]
      simp [d0,d1,hd0,hd1]
  intro i
  by_cases hi0 : i = 0
  · subst i
    have htarget : sideBit (d1pow L ++ lh) 0 = true := by
      rw [sideBit_append]
      have hlen : (d1pow L).length = 3*L := by simp [d1pow_length]
      have hlt : 0 < (d1pow L).length := by omega
      simp [hlt]
      exact sideBit_d1pow_true L 0 (by omega)
    calc
      outerLCIncSourceT3 T h a 2 0 h1 =
          afterLIncBridge T2 h1 h1 := hT3eq 0
      _ = true := by simp [afterLIncBridge]
      _ = sideBit (d1pow L ++ lh) 0 := htarget.symm
  · by_cases hi1 : i = 1
    · subst i
      have htarget : sideBit (d1pow L ++ lh) 1 = true := by
        rw [sideBit_append]
        have hlen : (d1pow L).length = 3*L := by simp [d1pow_length]
        have hlt : 1 < (d1pow L).length := by omega
        simp [hlt]
        exact sideBit_d1pow_true L 1 (by omega)
      calc
        outerLCIncSourceT3 T h a 2 0 (h1-1) =
            afterLIncBridge T2 h1 (h1-1) := hT3eq 1
        _ = true := by simp [afterLIncBridge]
        _ = sideBit (d1pow L ++ lh) 1 := htarget.symm
    · have hi2 : 2 ≤ i := by omega
      have hn0 : h1-(i:Int) ≠ h1-1 := by omega
      have hn1 : h1-(i:Int) ≠ h1 := by omega
      have hn2 : h1-(i:Int) ≠ h1+1 := by omega
      calc
        outerLCIncSourceT3 T h a 2 0 (h1-(i:Int)) =
            afterLIncBridge T2 h1 (h1-(i:Int)) := hT3eq i
        _ = T2 (h1-(i:Int)) := by
          simp [afterLIncBridge,hn0,hn1,hn2]
        _ = sideBit (d0 ++ (d1pow (L-1) ++ lh)) i := hT2left i
        _ = sideBit (d1 ++ (d1pow (L-1) ++ lh)) i := hbit i hi2
        _ = sideBit (d1pow L ++ lh) i := by rw [← hword]

/-- The two-step zero boundary does not alter any cell strictly left of h+5. -/
private theorem outerLCIncAfterZero_preserves_left
    (T : Int → Bool) (h : Int) (a m : Nat) (x : Int)
    (hx : x < h+5) :
    outerLCIncAfterZero T h a m x =
      outerLCIncAfterFive T h a m x := by
  have hnot : outerLCIncZeroInside (x-(h+5)) = false := by
    simp [outerLCIncZeroInside]
    omega
  simp [outerLCIncAfterZero,frameAt_tape,hnot]

/-- The five-step marker frame does not alter cells left of its start. -/
private theorem outerLCIncAfterFive_preserves_left
    (T : Int → Bool) (h : Int) (a m : Nat) (x : Int)
    (hx : x < outerLCIncH1 h a m+2) :
    outerLCIncAfterFive T h a m x = T x := by
  have hnot : outerLCIncFiveInside
      (x-(outerLCIncH1 h a m+2)) = false := by
    simp [outerLCIncFiveInside]
    omega
  simp [outerLCIncAfterFive,frameAt_tape,hnot]

/-- Exact local output of the five-step frame, at offsets 0 through 4. -/
private theorem outerLCIncAfterFive_local
    (T : Int → Bool) (h : Int) (a m k : Nat) (hk : k ≤ 4) :
    outerLCIncAfterFive T h a m
      (outerLCIncH1 h a m+2+(k:Int)) =
      if k=2 ∨ k=4 then true else false := by
  interval_cases k <;>
    norm_num [outerLCIncAfterFive,frameAt_tape,
      outerLCIncFiveInside,outerLCIncFiveEnd]

/--
The six cells immediately after the zero-valuation H-run are exactly
the marker-1/d0 boundary in head-facing order.
-/
private theorem outerLCIncAfterZero_m2_middleCell
    (T : Int → Bool) (h : Int) (a k : Nat) (hk : k < 6)
    (hT3right : T (outerLCIncH1 h a 2+1) = true) :
    outerLCIncAfterZero T h a 2
      (outerLCIncH1 h a 2+6-(k:Int)) =
      sideBit (markerWord 1 ++ d0) k := by
  let h1 : Int := outerLCIncH1 h a 2
  have hxleft : h1+6-(k:Int) < h+5 := by
    dsimp [h1,outerLCIncH1]
    omega
  rw [outerLCIncAfterZero_preserves_left T h a 2 _ hxleft]
  by_cases hk5 : k=5
  · subst k
    have hpres := outerLCIncAfterFive_preserves_left T h a 2 (h1+1) (by omega)
    rw [hpres]
    have hbridge : T (h1+1) = true := by
      simpa [h1] using hT3right
    have htarget : sideBit (markerWord 1 ++ d0) 5 = true := by
      simp [sideBit,markerWord,d0]
    calc
      outerLCIncAfterZero T h a 2 (h1+1) =
          outerLCIncAfterFive T h a 2 (h1+1) :=
        outerLCIncAfterZero_preserves_left T h a 2 (h1+1) (by omega)
      _ = T (h1+1) :=
        outerLCIncAfterFive_preserves_left T h a 2 (h1+1) (by omega)
      _ = true := hbridge
      _ = sideBit (markerWord 1 ++ d0) 5 := htarget.symm
  · have hk4 : k ≤ 4 := by omega
    have hcoord :
        h1+6-(k:Int) = h1+2+((4-k):Int) := by omega
    rw [hcoord]
    have hlocal := outerLCIncAfterFive_local T h a 2 (4-k) (by omega)
    rw [hlocal]
    interval_cases k <;> norm_num [sideBit,markerWord,d0]

/--
The left-facing tape at the pre-sweep head h+5 is
d1^(a+2) ++ markerWord(1) ++ d0 ++ d1^L ++ lh.
The E scan supplies the long d1 run, the five-step frame and H-run bridge
supply markerWord(1) ++ d0, and the zero-valuation H-run supplies d1^L ++ lh.
-/
theorem outerLCIncAfterZero_leftFacing_m2
    (L a b : Nat) (h : Int) (hL : 0 < L) :
    ∀ i : Nat,
      outerLCIncAfterZero
        (outerLCIncSourceT3 (s1Config L 1 2 a 0 b h).tape h a 2 0)
        h a 2 (h+5-(i:Int)) =
      sideBit
        (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i := by
  let T : Int → Bool := (s1Config L 1 2 a 0 b h).tape
  let T3 : Int → Bool := outerLCIncSourceT3 T h a 2 0
  let h1 : Int := outerLCIncH1 h a 2
  rcases outerLCInc_s1_postlude_conditions L 1 2 a b 0 h (by omega) with
    ⟨_,hscan,_,_,_,_⟩
  have hT3right : T3 (h1+1) = true := by
    change lbinDecHRunTape 0 (outerLCIncSourceT2 T h a 2) h1 (h1+1) = true
    simp [lbinDecHRunTape,sweptLeft,sweptRightB,afterLIncBridge]
  have hprefixLen :
      (d1pow (a+2) ++ (markerWord 1 ++ d0)).length = 3*a+12 := by
    simp [d1pow_length,markerWord,d0]
  have htargetOne (i : Nat) (hi : i < 3*(a+2)) :
      sideBit (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++
        (d1pow L ++ lh))) i = true := by
    rw [sideBit_append]
    have hlen : (d1pow (a+2)).length = 3*(a+2) := by
      simp [d1pow_length]
    have hlt : i < (d1pow (a+2)).length := by omega
    simp [hlt]
    exact sideBit_d1pow_true (a+2) i hi
  have htargetMiddle (i k : Nat) (hk : k < 6)
      (hcoord : i=3*(a+2)+k) :
      sideBit (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++
        (d1pow L ++ lh))) i =
      sideBit (markerWord 1 ++ d0) k := by
    rw [hcoord,sideBit_append]
    have hlen1 : (d1pow (a+2)).length = 3*(a+2) := by
      simp [d1pow_length]
    have hnot1 : ¬ 3*(a+2)+k < (d1pow (a+2)).length := by omega
    have hsub1 : 3*(a+2)+k-(d1pow (a+2)).length = 6+k := by
      rw [hlen1]
      omega
    simp [hnot1,hsub1]
    rw [sideBit_append]
    have hlen2 : (markerWord 1 ++ d0).length = 6 := by
      simp [markerWord,d0]
    have hnot2 : ¬ 6+k < (markerWord 1 ++ d0).length := by omega
    have hsub2 : 6+k-(markerWord 1 ++ d0).length = k := by
      rw [hlen2]
      omega
    simp [hnot2,hsub2]
  have htargetTail (i j : Nat) (hj : 3*a+12 ≤ i)
      (hcoord : i=3*a+12+j) :
      sideBit (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++
        (d1pow L ++ lh))) i =
      sideBit (d1pow L ++ lh) j := by
    have hword :
        d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh)) =
        (d1pow (a+2) ++ (markerWord 1 ++ d0)) ++ (d1pow L ++ lh) := by
      simp [List.append_assoc]
    rw [hword,sideBit_append]
    have hnot : ¬ i < (d1pow (a+2) ++ (markerWord 1 ++ d0)).length := by
      rw [hprefixLen]
      omega
    have hsub :
        i-(d1pow (a+2) ++ (markerWord 1 ++ d0)).length = j := by
      rw [hprefixLen]
      omega
    simp [hnot,hsub]
  intro i
  by_cases hi0 : i=0
  · subst i
    have hcell := outerLCIncAfterZero_cells T3 h a 2
    have htarget := htargetOne 0 (by omega)
    exact hcell.1.trans htarget.symm
  · by_cases hishort : i < 3*(a+2)
    · let j : Nat := 3*a+5-i
      have hj : j < 3*a+2+3 := by
        dsimp [j]
        omega
      have hcoord : h1+7+(j:Int) = h+5-(i:Int) := by
        dsimp [j,h1,outerLCIncH1]
        omega
      have hpres := outerLCIncAfterZero_preserves_left T3 h a 2
        (h+5-(i:Int)) (by omega)
      have hscanCell := hscan j hj
      rw [hcoord] at hscanCell
      calc
        outerLCIncAfterZero T3 h a 2 (h+5-(i:Int)) =
            outerLCIncAfterFive T3 h a 2 (h+5-(i:Int)) := hpres
        _ = true := hscanCell
        _ = sideBit
            (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i :=
          (htargetOne i hishort).symm
    · by_cases himid : i < 3*a+12
      · let k : Nat := i-(3*a+6)
        have hk : k<6 := by dsimp [k]; omega
        have hcoordI : i=3*(a+2)+k := by dsimp [k]; omega
        have hcoordX :
            h+5-(i:Int) = h1+6-(k:Int) := by
          dsimp [k,h1,outerLCIncH1]
          omega
        have hcell := outerLCIncAfterZero_m2_middleCell T3 h a k hk hT3right
        rw [hcoordX] at hcell
        calc
          outerLCIncAfterZero T3 h a 2 (h+5-(i:Int)) =
              sideBit (markerWord 1 ++ d0) k := by
                simpa [T3] using hcell
          _ = sideBit
              (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i :=
            (htargetMiddle i k hk hcoordI).symm
      · let j : Nat := i-(3*a+12)
        have hj : 3*a+12 ≤ i := by dsimp [j]; omega
        have hcoordX :
            h+5-(i:Int) = h1-(j:Int) := by
          dsimp [j,h1,outerLCIncH1]
          omega
        have hpres0 := outerLCIncAfterZero_preserves_left T3 h a 2
          (h+5-(i:Int)) (by omega)
        have hpres5 := outerLCIncAfterFive_preserves_left T3 h a 2
          (h+5-(i:Int)) (by dsimp [h1,outerLCIncH1]; omega)
        have hleft := outerLCIncSourceT3_leftFacing_m2 L a b h hL j
        have htarget := htargetTail i j hj (by dsimp [j]; omega)
        calc
          outerLCIncAfterZero T3 h a 2 (h+5-(i:Int)) =
              outerLCIncAfterFive T3 h a 2 (h+5-(i:Int)) := hpres0
          _ = T3 (h+5-(i:Int)) := hpres5
          _ = sideBit (d1pow L ++ lh) j := by
            rw [hcoordX]
            simpa [T3] using hleft
          _ = sideBit
              (d1pow (a+2) ++ ((markerWord 1 ++ d0) ++ (d1pow L ++ lh))) i :=
            htarget.symm


end BB6Coverage.Agent42OuterLCInc
