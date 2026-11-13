import Rst1PrimeBridge9Source
import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Source-level bridge 6 after the fourth counted sweep in Rst1'

This file continues the already source-connected chain through bridge9 and
the following (a+1)-block right sweep. It proves bridge6's local input
window from the original S1 source and composes the six-step bridge.
-/

namespace BB6Coverage.Agent8Rst1PrimeTail

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent8Rst1Prime
open BB6Coverage.Agent4Rst1Prime
open BB6Coverage.Agent6Q4Prefix

/-- After bridge9, every cell strictly to the right of the original
right-hand sentinel region is still the original S1 source cell. -/
theorem rst1PrimeAfterBridge9_eq_source_right
    (L a b : Nat) (h x : Int) (hx : h+1 < x) :
    (rst1PrimeAfterBridge9 L a b h).tape x =
      (s1Config L 0 1 a 0 b h).tape x := by
  let H0 : Int := h-((3*a+1:Int))
  let H1 : Int := H0-2
  let H2 : Int := H1-((3*L+5:Int))
  let H3 : Int := H2+4
  change
    (frameAt
      (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3)
      H0 inside9 bridge9End).tape x =
      (s1Config L 0 1 a 0 b h).tape x
  have hrel9 : x-H0 = x-(h-((3*a+1:Int))) := by
    dsimp [H0]
  have hout9 : inside9 (x-H0) = false := by
    simp [inside9,inWindow,hrel9]
    dsimp [H0]
    omega
  rw [frameAt_tape]
  simp only [hout9]
  have hafter3 :
      sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape H3 x =
        (rst1PrimeAfterBridge20 L a b h).tape x := by
    apply rst1Prime_sweptRight_preserves_after
    dsimp [H0,H1,H2,H3]
    omega
  rw [hafter3]
  change
    (frameAt
      (sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape H1)
      H2 inside20 bridge20End).tape x =
      (s1Config L 0 1 a 0 b h).tape x
  have hout20 : inside20 (x-H2) = false := by
    simp [inside20,inWindow]
    dsimp [H0,H1,H2]
    omega
  rw [frameAt_tape]
  simp only [hout20]
  have hleft2 :
      sweptLeft (3*L+5) (rst1PrimeAfterBridge8 L a b h).tape H1 x =
        (rst1PrimeAfterBridge8 L a b h).tape x := by
    apply sweptLeft_eq_of_gt
    dsimp [H0,H1]
    omega
  rw [hleft2]
  change
    (frameAt
      (sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h)
      H0 inside8 bridge8End).tape x =
      (s1Config L 0 1 a 0 b h).tape x
  have hout8 : inside8 (x-H0) = false := by
    simp [inside8,inWindow]
    dsimp [H0]
    omega
  rw [frameAt_tape]
  simp only [hout8]
  apply sweptLeft_eq_of_gt
  exact hx

/-- Full configuration after the (a+1)-block right sweep following
bridge9. -/
def rst1PrimeAfterRightSweepA
    (L a b : Nat) (h : Int) : Config :=
  ⟨3,
    (h-((3*a+1:Int))+3)+3*((a+1):Int),
    sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape
      (h-((3*a+1:Int))+3)⟩

/-- Reuse Agent 4's exact original-source run through the fourth sweep. -/
theorem rst1Prime_rightSweep_after_bridge9_run_source
    (L a b : Nat) (h : Int) :
    run tm2
      (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9+3*(a+1))
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterRightSweepA L a b h) := by
  simpa [rst1PrimeAfterRightSweepA] using
    rst1Prime_rightSweep_after_bridge9_run L a b h

/-- The fourth sweep's endpoint is h+5. -/
theorem rst1PrimeAfterRightSweepA_head
    (L a b : Nat) (h : Int) :
    (rst1PrimeAfterRightSweepA L a b h).head = h+5 := by
  simp [rst1PrimeAfterRightSweepA]
  omega

/-- Bridge6 sees its exact five-cell source window after the fourth
counted sweep. -/
theorem rst1Prime_bridge6_window_after_rightSweep
    (L a b : Nat) (h : Int) :
    ∀ x, inside6 x = true →
      (rst1PrimeAfterRightSweepA L a b h).tape
        (((h-((3*a+1:Int))+3)+3*((a+1):Int))+x) =
        decide (x ∈ bridge6Start.marked) := by
  let H0 : Int := h-((3*a+1:Int))
  let Hs : Int := H0+3
  let H6 : Int := Hs+3*((a+1):Int)
  intro x hx
  have hxw : -1 ≤ x ∧ x ≤ 3 := by
    simpa [inside6,inWindow] using hx
  have hcases : x=(-1:Int) ∨ x=0 ∨ x=1 ∨ x=2 ∨ x=3 := by omega
  change
    sweptRight (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs
      (H6+x) = decide (x ∈ bridge6Start.marked)
  rcases hcases with hneg | hzero | hone | htwo | hthree
  · subst x
    have hlast := rst1Prime_sweptRight_lastBlock a
      (rst1PrimeAfterBridge9 L a b h).tape Hs
    have hcoord : H6+(-1:Int) = Hs+3*(a:Int)+2 := by
      dsimp [H6,Hs,H0]
      omega
    rw [hcoord]
    simpa [bridge6Start] using hlast.2.2
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs H6 (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h H6 (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6 = h+5 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 4
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs (H6+1) (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h (H6+1) (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6+1 = h+1+5 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 5
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs (H6+2) (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h (H6+2) (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6+2 = h+1+6 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 6
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (a+1) (rst1PrimeAfterBridge9 L a b h).tape Hs (H6+3) (by
        dsimp [H6,Hs,H0]
        omega)
    rw [hafter]
    have hsource := rst1PrimeAfterBridge9_eq_source_right
      L a b h (H6+3) (by dsimp [H6,Hs,H0]; omega)
    rw [hsource]
    have hcoord : H6+3 = h+1+7 := by dsimp [H6,Hs,H0]; omega
    rw [hcoord]
    have hcell := s1Config_right_cell L 0 1 a 0 b h 7
    simpa [bridge6Start,s1PhysicalRight,s0PhysicalRight,
      s0RightFacing,sideBit] using hcell

/-- Full configuration after bridge6. -/
def rst1PrimeAfterBridge6
    (L a b : Nat) (h : Int) : Config :=
  frameAt (rst1PrimeAfterRightSweepA L a b h).tape
    ((h-((3*a+1:Int))+3)+3*((a+1):Int))
    inside6 bridge6End

/-- Compose the fourth sweep with the exact six-step bridge6. -/
theorem rst1Prime_bridge6_after_rightSweep
    (L a b : Nat) (h : Int) :
    run tm2
      (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9+3*(a+1)+6)
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterBridge6 L a b h) := by
  rw [run_add,rst1Prime_rightSweep_after_bridge9_run_source]
  simp only [Option.bind_some]
  exact bridge6_at (rst1PrimeAfterRightSweepA L a b h).tape
    ((h-((3*a+1:Int))+3)+3*((a+1):Int))
    (rst1Prime_bridge6_window_after_rightSweep L a b h)

#print axioms rst1PrimeAfterBridge9_eq_source_right
#print axioms rst1Prime_rightSweep_after_bridge9_run_source
#print axioms rst1Prime_bridge6_window_after_rightSweep
#print axioms rst1Prime_bridge6_after_rightSweep

end BB6Coverage.Agent8Rst1PrimeTail
