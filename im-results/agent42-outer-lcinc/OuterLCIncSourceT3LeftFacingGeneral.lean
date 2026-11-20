import OuterLCIncPrelude
import OuterLCIncPostludeSource
import LBinDecHRunLeftFacing
import Lean.Elab.Tactic.Omega

/-!
# Generic outer-LCInc source H-run decrement

This theorem closes the source-side H-run for every valid outer
counter n, every source marker m<3, and every left unary width a.
The marker bridge preserves the carry-prefix input; the generic
counted H-run changes

  d1pow r ++ d0 ++ BinDec(len,q)

to

  d0pow r ++ d1 ++ BinDec(len,q),

which is exactly BinDec(L,n-1).  It is the first reusable step needed
to extend the canonical postlude endpoint beyond the old n=1,m=2
specialization.

This is an intermediate source theorem and has not been locally
compiled in the current invocation.
-/

namespace BB6Coverage.Agent42OuterLCInc

open BB6Coverage
open BB6Coverage.Agent8OuterLCInc
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24LBinDecHRun
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent48Champion

/-- For every valid positive source counter, the actual T3 tape has
the exact head-facing encoding of n-1 on its left side. -/
theorem outerLCIncSourceT3_leftFacing_general
    (L n m a b : Nat) (h : Int)
    (hm : m < 3) (hn0 : 0 < n) (hnlt : n < 2^L) :
    ∀ i : Nat,
      outerLCIncSourceT3 (s1Config L n m a 0 b h).tape h a m (v2 n)
        (outerLCIncH1 h a m-(i:Int)) =
      sideBit (binDec L (n-1) ++ lh) i := by
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
      (by simpa [h1,outerLCIncH1] using hx)
    simpa [T2,outerLCIncSourceT2,outerLCIncSourceT1,T] using hp
  have hright : T2 (h1+1)=false := by
    have hp := markerBridgeFrameOut_right_zero m hm
      (outerLCIncSourceT1 T h a) (h-(3*a:Int))
    simpa [T2,outerLCIncSourceT2,outerLCIncSourceT1,T,h1,
      outerLCIncH1] using hp
  have hleft : ∀ i : Nat,
      T2 (h1-(i:Int)) =
        sideBit (d1pow r ++ (d0 ++ (binDec len q ++ lh))) i := by
    intro i
    have hp := hpres (h1-(i:Int)) (by omega)
    have hc := outer_s1_counter_carry_cell L n m a b h hm q r len i
      hn hL hq
    have hcoord : h1-(i:Int)=h-((3*a+m+5+i):Int) := by
      dsimp [h1,outerLCIncH1]
      omega
    calc
      T2 (h1-(i:Int)) = T (h1-(i:Int)) := hp
      _ = sideBit (d1pow r ++ (d0 ++ (binDec len q ++ lh))) i := by
        rw [hcoord]
        simpa [T,List.append_assoc] using hc
  have hrun := lbinDecHRunTape_leftFacing_of_input r T2 h1
    (binDec len q ++ lh) hright hleft
  have hbin : binDec L (n-1) =
      d0pow r ++ (d1 ++ binDec len q) := by
    rw [hL,hn]
    exact binDec_sub_one_carryPrefix len q r hq
  intro i
  change outerLCIncSourceT3 T h a m (v2 n)
      (outerLCIncH1 h a m-(i:Int)) =
    sideBit (binDec L (n-1) ++ lh) i
  rw [hv2]
  have hT3 : outerLCIncSourceT3 T h a m r =
      lbinDecHRunTape r T2 h1 := by
    rfl
  rw [hT3,hbin]
  simpa [List.append_assoc] using hrun i

#print axioms outerLCIncSourceT3_leftFacing_general

end BB6Coverage.Agent42OuterLCInc
