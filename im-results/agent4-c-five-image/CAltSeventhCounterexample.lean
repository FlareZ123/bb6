import CAltSixthStrict
import Lean.Elab.Tactic.Omega

namespace BB6.Agent4Five
open BB6.Agent46

/-- Exact genuine original-section witness that a naive SECOND direct
    lift of the new fifth/sixth cone is no longer a strict sixth/seventh
    image gap: the target (1,574) has an eight-edge incoming chain.
    This is a counterexample to extrapolating unique-parent inheritance
    through another lift without controlling high-bounce alternatives. -/
theorem second_lift_has_eight_incoming_edges :
    secNext (810,143)=some (524,288) ∧
    secNext (524,288)=some (997,55) ∧
    secNext (997,55)=some (887,112) ∧
    secNext (887,112)=some (663,226) ∧
    secNext (663,226)=some (211,454) ∧
    secNext (211,454)=some (581,274) ∧
    secNext (581,274)=some (33,550) ∧
    secNext (33,550)=some (1,574) := by
  decide

/-- The first-generation image seed is strictly fifth/sixth at (573,286),
    yet its second direct descendant (1,574) lies in the eighth source image. -/
theorem second_lift_gap_noninheritance :
    secNext (573,286)=some (1,574) ∧
    (∃ a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 a7 b7,
      secNext (a0,b0)=some (a1,b1) ∧
      secNext (a1,b1)=some (a2,b2) ∧
      secNext (a2,b2)=some (a3,b3) ∧
      secNext (a3,b3)=some (a4,b4) ∧
      secNext (a4,b4)=some (a5,b5) ∧
      secNext (a5,b5)=some (a6,b6) ∧
      secNext (a6,b6)=some (a7,b7) ∧
      secNext (a7,b7)=some (1,574)) := by
  constructor
  · decide
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := second_lift_has_eight_incoming_edges
  exact ⟨810,143,524,288,997,55,887,112,663,226,
    211,454,581,274,33,550,h0,h1,h2,h3,h4,h5,h6,h7⟩

#print axioms second_lift_has_eight_incoming_edges
#print axioms second_lift_gap_noninheritance
end BB6.Agent4Five
