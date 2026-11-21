import M1EvenValuationBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent8M1EvenValuationBridgeFootprint

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48M1EvenValuationBridge
open BB6Coverage.Agent48M1EvenValuationSweep
open BB6Coverage.Agent24M1EvenValuationBridge

/-- The valuation macro leaves the entire tape strictly to the left of its
    three-cell setup window untouched. -/
theorem m1EvenValuationBridgeTape_preserves_far_left
    (v : Nat) (T : Int → Bool) (h x : Int)
    (hx : x < h - ((3*(v+1)+3 : Nat) : Int)) :
    m1EvenValuationBridgeTape v T h x = T x := by
  let N : Nat := 3*(v+1)
  let x0 : Int := h-(N:Int)
  let Tleft : Int → Bool := state1SweptLeft N T h
  let Tsetup : Int → Bool := valuationSetupTape Tleft x0
  let Tright : Int → Bool := state5SweptRight (v+1) Tsetup (x0+1)
  have hleft : Tleft x = T x := by
    dsimp [Tleft]
    apply state1SweptLeft_preserves_left N T h x
    dsimp [N,x0] at hx ⊢
    omega
  have hsetup : Tsetup x = Tleft x := by
    dsimp [Tsetup,valuationSetupTape]
    have hne0 : x ≠ x0 := by dsimp [x0,N]; omega
    have hne1 : x ≠ x0-1 := by dsimp [x0,N]; omega
    have hne2 : x ≠ x0-2 := by dsimp [x0,N]; omega
    have hne3 : x ≠ x0-3 := by dsimp [x0,N]; omega
    simp [hne0,hne1,hne2,hne3]
  have hright : Tright x = Tsetup x := by
    dsimp [Tright]
    apply state5SweptRight_preserves_left (v+1) Tsetup (x0+1) x
    dsimp [x0,N] at hx ⊢
    omega
  have hexit : valuationExit1Tape Tright (h+1) x = Tright x := by
    simp [valuationExit1Tape]
    dsimp [x0,N] at hx ⊢
    omega
  unfold m1EvenValuationBridgeTape
  change valuationExit1Tape Tright (h+1) x = T x
  rw [hexit,hright,hsetup,hleft]

/-- The full macro footprint is contained in the half-open interval from
    three cells left of the left-sweep endpoint through the first two cells
    to the right of the original head. -/
theorem m1EvenValuationBridgeTape_outside_footprint
    (v : Nat) (T : Int → Bool) (h x : Int)
    (hx : x < h - ((3*(v+1)+3 : Nat) : Int) ∨ h+2 ≤ x) :
    m1EvenValuationBridgeTape v T h x = T x := by
  rcases hx with hleft | hright
  · exact m1EvenValuationBridgeTape_preserves_far_left v T h x hleft
  · exact m1EvenValuationBridgeTape_preserves_right v T h x hright

#print axioms m1EvenValuationBridgeTape_preserves_far_left
#print axioms m1EvenValuationBridgeTape_outside_footprint

end BB6Coverage.Agent8M1EvenValuationBridgeFootprint
