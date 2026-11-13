import Rst1PrimeBridge20Source
import CountedRst1Prime
import Lean.Elab.Tactic.Omega

/-!
# Source-level bridge9 after the first Rst1' right sweep

The 3a+1 left sweep, bridge8, 3L+5 left sweep, bridge20, and L+1
right sweep return the head to the first sweep's new head.  The five
cells around that head are exactly the input frame for bridge9.  This
module lifts that finite bridge to the original infinite-tape semantics.
-/

namespace BB6Coverage.Agent24Rst1PrimeBridge9

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent4Rst1Prime

/-- The cell immediately right of the endpoint of any positive left
sweep is blank. -/
theorem rst1Prime_sweptLeft_head_plus1_false
    (n : Nat) (T : Int → Bool) (h : Int) :
    sweptLeft (n+1) T h (h-((n+1:Int))+1) = false := by
  induction n generalizing T h with
  | zero =>
      have hcoord : h-((1:Int))+1 = h := by omega
      rw [sweptLeft, hcoord]
      simp [holeThree]
  | succ n ih =>
      have hcoord :
          h-((n+2:Int))+1 = (h-1)-((n+1:Int))+1 := by omega
      rw [sweptLeft, hcoord]
      exact ih (holeThree T h) (h-1)

/-- The configuration after the bridge9 finite frame is applied. -/
def rst1PrimeAfterBridge9 (L a b : Nat) (h : Int) : Config :=
  let H0 : Int := h-((3*a+1:Int))
  let H1 : Int := H0-2
  let H2 : Int := H1-((3*L+5:Int))
  let Hs : Int := H2+4
  frameAt
    (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape Hs)
    (Hs+3*((L+1):Int)) inside9 bridge9End

/-- After the L+1-block right sweep, the complete bridge9 query window
is exactly bridge9Start.  The last scanned triple supplies the two zeros;
the three cells at and beyond the new head are inherited from bridge8's
output / the first counted sweep. -/
theorem rst1Prime_bridge9_window_after_rightSweep
    (L a b : Nat) (h : Int) :
    ∀ x, inside9 x = true →
      (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape
        (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4))
        ((((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)
          +3*((L+1):Int)+x) =
      decide (x ∈ bridge9Start.marked) := by
  let H0 : Int := h-((3*a+1:Int))
  let H1 : Int := H0-2
  let H2 : Int := H1-((3*L+5:Int))
  let Hs : Int := H2+4
  let T2 : Int → Bool := (rst1PrimeAfterBridge20 L a b h).tape
  have hhead : Hs+3*((L+1):Int) = H0 := by
    dsimp [Hs,H2,H1,H0]
    omega
  change ∀ x, inside9 x = true →
    (sweptRight (L+1) T2 Hs)
      (Hs+3*((L+1):Int)+x) =
        decide (x ∈ bridge9Start.marked)

  have hlast := rst1Prime_sweptRight_lastBlock L T2 Hs

  have hpres (k : Nat) :
      sweptRight (L+1) T2 Hs (H0+(k:Int)) =
        T2 (H0+(k:Int)) := by
    apply rst1Prime_sweptRight_preserves_after
    rw [← hhead]
    omega

  have hT0 : T2 H0 = true := by
    dsimp [T2,rst1PrimeAfterBridge20]
    have hrel20 : H0-H2 = 3*(L:Int)+7 := by
      dsimp [H2,H1]
      omega
    have hout20 : inside20 (H0-H2) = false := by
      rw [hrel20]
      simp [inside20,inWindow]
      omega
    rw [frameAt_tape]
    simp only [hout20]
    have hunchanged2 :
        sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
          H1 H0 =
        (rst1PrimeAfterBridge8 L a b h).tape H0 := by
      apply sweptLeft_eq_of_gt
      dsimp [H1,H0]
      omega
    rw [hunchanged2]
    dsimp [rst1PrimeAfterBridge8]
    rw [frameAt_tape]
    simp [inside8,inWindow,bridge8End]

  have hT1 : T2 (H0+1) = false := by
    dsimp [T2,rst1PrimeAfterBridge20]
    have hrel20 : (H0+1)-H2 = 3*(L:Int)+8 := by
      dsimp [H2,H1]
      omega
    have hout20 : inside20 ((H0+1)-H2) = false := by
      rw [hrel20]
      simp [inside20,inWindow]
      omega
    rw [frameAt_tape]
    simp only [hout20]
    have hunchanged2 :
        sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
          H1 (H0+1) =
        (rst1PrimeAfterBridge8 L a b h).tape (H0+1) := by
      apply sweptLeft_eq_of_gt
      dsimp [H1,H0]
      omega
    rw [hunchanged2]
    dsimp [rst1PrimeAfterBridge8]
    rw [frameAt_tape]
    have hout8 : inside8 ((H0+1)-H0) = false := by
      simp [inside8,inWindow]
    simp only [hout8]
    have hfirst :
        sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h
          (H0+1) = false := by
      have htmp := rst1Prime_sweptLeft_head_plus1_false
        (3*a) (s1Config L 0 1 a 0 b h).tape h
      simpa [H0] using htmp
    exact hfirst

  have hT2 : T2 (H0+2) = true := by
    dsimp [T2,rst1PrimeAfterBridge20]
    have hrel20 : (H0+2)-H2 = 3*(L:Int)+9 := by
      dsimp [H2,H1]
      omega
    have hout20 : inside20 ((H0+2)-H2) = false := by
      rw [hrel20]
      simp [inside20,inWindow]
      omega
    rw [frameAt_tape]
    simp only [hout20]
    have hunchanged2 :
        sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape
          H1 (H0+2) =
        (rst1PrimeAfterBridge8 L a b h).tape (H0+2) := by
      apply sweptLeft_eq_of_gt
      dsimp [H1,H0]
      omega
    rw [hunchanged2]
    dsimp [rst1PrimeAfterBridge8]
    rw [frameAt_tape]
    have hout8 : inside8 ((H0+2)-H0) = false := by
      simp [inside8,inWindow]
    simp only [hout8]
    have hfirst :
        sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h
          (H0+2) = true := by
      have htmp := sweptLeft_one_block
        (3*a+1) (s1Config L 0 1 a 0 b h).tape h 0 (by omega)
      simpa [H0] using htmp
    exact hfirst

  intro x hx
  have hxw : -2 ≤ x ∧ x ≤ 2 := by
    simpa [inside9,inWindow] using hx
  have hcases :
      x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by omega
  rcases hcases with hneg2 | hneg1 | hzero | hone | htwo
  · subst x
    have hcoord :
        Hs+3*((L+1):Int)+(-2:Int) =
          Hs+3*(L:Int)+1 := by omega
    rw [hcoord]
    simpa [bridge9Start] using hlast.2.1
  · subst x
    have hcoord :
        Hs+3*((L+1):Int)+(-1:Int) =
          Hs+3*(L:Int)+2 := by omega
    rw [hcoord]
    simpa [bridge9Start] using hlast.2.2
  · subst x
    have hcoord :
        Hs+3*((L+1):Int)+(0:Int) = H0 := by omega
    rw [hcoord]
    simpa [bridge9Start] using (hpres 0).trans hT0
  · subst x
    have hcoord :
        Hs+3*((L+1):Int)+(1:Int) = H0+1 := by omega
    rw [hcoord]
    simpa [bridge9Start] using (hpres 1).trans hT1
  · subst x
    have hcoord :
        Hs+3*((L+1):Int)+(2:Int) = H0+2 := by omega
    rw [hcoord]
    simpa [bridge9Start] using (hpres 2).trans hT2

/-- Compose the first three Rst1' sweeps and bridge9 into an exact
original-machine run on the entire infinite source tape. -/
theorem rst1Prime_bridge9_after_rightSweep
    (L a b : Nat) (h : Int) :
    run tm2 (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9)
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterBridge9 L a b h) := by
  have hprefix := rst1Prime_rightSweep_after_bridge20_run L a b h
  rw [run_add,hprefix]
  simp only [Option.bind_some]
  exact bridge9_at
    (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4))
    ((((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)
      +3*((L+1):Int))
    (rst1Prime_bridge9_window_after_rightSweep L a b h)

theorem rst1Prime_cost_through_bridge9 (L a b : Nat) :
    9*a+3+8+3*(3*L+5)+20+3*(L+1)+9 =
      58+12*L+9*a := by omega

#print axioms rst1Prime_sweptLeft_head_plus1_false
#print axioms rst1Prime_bridge9_window_after_rightSweep
#print axioms rst1Prime_bridge9_after_rightSweep
#print axioms rst1Prime_cost_through_bridge9

end BB6Coverage.Agent24Rst1PrimeBridge9
