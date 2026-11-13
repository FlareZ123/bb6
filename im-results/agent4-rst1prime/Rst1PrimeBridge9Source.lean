import Rst1PrimeBridge20Source
import CountedRst1Prime
import Lean.Elab.Tactic.Omega

/-!
# Source-level bridge9 after the first rightward sweep in Rst1'

The first rightward sweep ends at the original post-first-sweep head H0.
Its final block gives two zeros immediately to the left.  The cells at
H0,H0+1,H0+2 are supplied by bridge8 and the first left sweep.  This
proves bridge9's full input window on the actual source tape and lifts
the nine-step bridge through the original-machine run.
-/

namespace BB6Coverage.Agent4Rst1Prime

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24ChampionTime
open BB6Coverage.Agent8Rst1Prime

/-- The tape immediately before bridge9 has the exact three cells at
and to the right of the phase-5 endpoint. -/
theorem rst1PrimeAfterBridge20_right_cells
    (L a b : Nat) (h : Int) :
    (rst1PrimeAfterBridge20 L a b h).tape
        (h-((3*a+1:Int))) = true ∧
    (rst1PrimeAfterBridge20 L a b h).tape
        (h-((3*a+1:Int))+1) = false ∧
    (rst1PrimeAfterBridge20 L a b h).tape
        (h-((3*a+1:Int))+2) = true := by
  let H0 : Int := h-((3*a+1:Int))
  let H1 : Int := H0-2
  let H2 : Int := H1-((3*L+5:Int))
  let T1 : Int → Bool :=
    sweptLeft (3*a+1) (s1Config L 0 1 a 0 b h).tape h
  let T2 : Int → Bool := frameAt T1 H0 inside8 bridge8End
  let T3 : Int → Bool := sweptLeft (3*L+5) T2 H1
  change (frameAt T3 H2 inside20 bridge20End).tape H0 = true ∧
    (frameAt T3 H2 inside20 bridge20End).tape (H0+1) = false ∧
    (frameAt T3 H2 inside20 bridge20End).tape (H0+2) = true
  have hrel0 : H0-H2 = 3*L+7 := by dsimp [H2,H1]; omega
  have hout0 : inside20 (H0-H2) = false := by
    simp [inside20,inWindow,hrel0]
    omega
  have hrel1 : (H0+1)-H2 = 3*L+8 := by dsimp [H2,H1]; omega
  have hout1 : inside20 ((H0+1)-H2) = false := by
    simp [inside20,inWindow,hrel1]
    omega
  have hrel2 : (H0+2)-H2 = 3*L+9 := by dsimp [H2,H1]; omega
  have hout2 : inside20 ((H0+2)-H2) = false := by
    simp [inside20,inWindow,hrel2]
    omega
  have hunchanged0 : T3 H0 = T2 H0 := by
    apply sweptLeft_eq_of_gt
    dsimp [H1]
    omega
  have hunchanged1 : T3 (H0+1) = T2 (H0+1) := by
    apply sweptLeft_eq_of_gt
    dsimp [H1]
    omega
  have hunchanged2 : T3 (H0+2) = T2 (H0+2) := by
    apply sweptLeft_eq_of_gt
    dsimp [H1]
    omega
  constructor
  · rw [frameAt_tape]
    simp only [hout0]
    rw [hunchanged0,frameAt_tape]
    simp [inside8,inWindow,bridge8End]
  constructor
  · rw [frameAt_tape]
    simp only [hout1]
    rw [hunchanged1,frameAt_tape]
    have hout8 : inside8 ((H0+1)-H0) = false := by
      simp [inside8,inWindow]
    simp only [hout8]
    have hfalse := sweptLeft_head_plus1_eq_false
      (3*a+1) (s1Config L 0 1 a 0 b h).tape h (by omega)
    simpa [T1,H0] using hfalse
  · rw [frameAt_tape]
    simp only [hout2]
    rw [hunchanged2,frameAt_tape]
    have hout8 : inside8 ((H0+2)-H0) = false := by
      simp [inside8,inWindow]
    simp only [hout8]
    have htrue := sweptLeft_one_block
      (3*a+1) (s1Config L 0 1 a 0 b h).tape h 0 (by omega)
    simpa [T1,H0] using htrue

/-- The full five-cell bridge9 input window after the first rightward
sweep. -/
theorem rst1Prime_bridge9_window_after_rightSweep
    (L a b : Nat) (h : Int) :
    ∀ x, inside9 x = true →
      (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape
        (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4))
        (h-((3*a+1:Int))+x) =
        decide (x ∈ bridge9Start.marked) := by
  intro x hx
  have hxw : -2 ≤ x ∧ x ≤ 2 := by
    simpa [inside9,inWindow] using hx
  have hcases : x=-2 ∨ x=-1 ∨ x=0 ∨ x=1 ∨ x=2 := by omega
  rcases hcases with h2 | h1 | h0 | hpos1 | hpos2
  · subst x
    have hlast := rst1Prime_sweptRight_lastBlock
      L (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)
    have hcoord :
        (h-((3*a+1:Int)))+(-2:Int) =
          (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)+
            3*((L:Int))+1 := by omega
    rw [hcoord]
    simpa [bridge9Start] using hlast.2.1
  · subst x
    have hlast := rst1Prime_sweptRight_lastBlock
      L (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)
    have hcoord :
        (h-((3*a+1:Int)))+(-1:Int) =
          (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)+
            3*((L:Int))+2 := by omega
    rw [hcoord]
    simpa [bridge9Start] using hlast.2.2
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (L+1) (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)
      (h-((3*a+1:Int)) ) (by omega)
    rw [hafter]
    have hcell := (rst1PrimeAfterBridge20_right_cells L a b h).1
    simpa [bridge9Start] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (L+1) (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)
      (h-((3*a+1:Int))+1) (by omega)
    rw [hafter]
    have hcell := (rst1PrimeAfterBridge20_right_cells L a b h).2.1
    simpa [bridge9Start] using hcell
  · subst x
    have hafter := rst1Prime_sweptRight_preserves_after
      (L+1) (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4)
      (h-((3*a+1:Int))+2) (by omega)
    rw [hafter]
    have hcell := (rst1PrimeAfterBridge20_right_cells L a b h).2.2
    simpa [bridge9Start] using hcell

/-- Full original-source configuration after bridge9. -/
def rst1PrimeAfterBridge9
    (L a b : Nat) (h : Int) : Config :=
  frameAt
    (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4))
    (h-((3*a+1:Int))) inside9 bridge9End

/-- Compose the phase-5 right sweep with the exact nine-step bridge. -/
theorem rst1Prime_bridge9_after_rightSweep
    (L a b : Nat) (h : Int) :
    run tm2 (9*a+3+8+3*(3*L+5)+20+3*(L+1)+9)
      (s1Config L 0 1 a 0 b h) =
      some (rst1PrimeAfterBridge9 L a b h) := by
  rw [run_add,rst1Prime_rightSweep_after_bridge20_run]
  simp only [Option.bind_some]
  exact bridge9_at
    (sweptRight (L+1) (rst1PrimeAfterBridge20 L a b h).tape
      (((h-((3*a+1:Int))-2)-((3*L+5:Int)))+4))
    (h-((3*a+1:Int)))
    (rst1Prime_bridge9_window_after_rightSweep L a b h)

#print axioms rst1PrimeAfterBridge20_right_cells
#print axioms rst1Prime_bridge9_window_after_rightSweep
#print axioms rst1PrimeAfterBridge9
#print axioms rst1Prime_bridge9_after_rightSweep

end BB6Coverage.Agent4Rst1Prime
