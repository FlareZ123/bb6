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
    rw [hT3eq]
    have htrue : sideBit (d1pow L) 0 = true :=
      sideBit_d1pow_true L 0 (by omega)
    simpa [afterLIncBridge] using htrue
  · by_cases hi1 : i = 1
    · subst i
      rw [hT3eq]
      have htrue : sideBit (d1pow L) 1 = true :=
        sideBit_d1pow_true L 1 (by omega)
      simpa [afterLIncBridge] using htrue
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

end BB6Coverage.Agent42OuterLCInc
