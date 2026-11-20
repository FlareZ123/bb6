import OuterLCIncSourceT3LeftFacingGeneral
import LBinDecHRunLeftFacing
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8OuterLCInc
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion

/-- The generic LBinDec H-run leaves its right-neighbor boundary cell
blank, for every valid outer counter and marker. -/
theorem outerLCIncSourceT3_rightPlus1_general
    (L n m a b : Nat) (h : Int)
    (hm : m < 3) (hn0 : 0 < n) (hnlt : n < 2^L) :
    outerLCIncSourceT3 (s1Config L n m a 0 b h).tape h a m (v2 n)
      (outerLCIncH1 h a m+1) = true := by
  obtain ⟨q,r,len,hn,hL,hq⟩ :=
    exists_odd_factor_bounded L n hn0 hnlt
  have hv2 : v2 n = r := by
    rw [hn]
    exact v2_odd_factor q r
  let T : Int → Bool := (s1Config L n m a 0 b h).tape
  let T2 : Int → Bool := outerLCIncSourceT2 T h a m
  let h1 : Int := outerLCIncH1 h a m
  have hpres : ∀ x : Int, x≤h1 → T2 x=T x := by
    intro x hx
    have hp := outer_markerBridge_preserves_source L n m a b h hm x
      (by dsimp [h1,outerLCIncH1]; omega)
    simpa [T2,outerLCIncSourceT2,outerLCIncSourceT1,T] using hp
  have hleftOnes : leftOnes T2 h1 (3*r) := by
    intro i hi
    have hp := hpres (h1-(i:Int)) (by omega)
    have hc := outer_s1_counter_carry_cell L n m a b h hm q r len i
      hn hL hq
    have hcoord : h1-(i:Int)=h-((3*a+m+5+i):Int) := by
      dsimp [h1,outerLCIncH1]
      omega
    have hbit :
        sideBit (d1pow r ++ (d0 ++ (binDec len q ++ lh))) i = true := by
      have hlt : i < (d1pow r).length := by
        rw [d1pow_length]
        omega
      rw [outer_sideBit_append_prefix _ _ _ hlt]
      exact outer_sideBit_d1pow r i (by rw [d1pow_length] at hi; exact hi)
    calc
      T2 (h1-(i:Int)) = T (h1-(i:Int)) := hp
      _ = sideBit (d1pow r ++ (d0 ++ (binDec len q ++ lh))) i := by
        rw [hcoord]
        simpa [T,List.append_assoc] using hc
      _ = true := hbit
  have hrun := lbinDecHRunTape_rightPlus1 r T2 h1 hleftOnes
  change outerLCIncSourceT3 T h a m (v2 n)
      (outerLCIncH1 h a m+1) = true
  rw [hv2]
  have hT3 : outerLCIncSourceT3 T h a m r =
      lbinDecHRunTape r T2 h1 := by
    rfl
  rw [hT3]
  simpa [h1,outerLCIncH1] using hrun

#print axioms outerLCIncSourceT3_rightPlus1_general

end BB6Coverage.Agent42OuterLCInc
