import ZipThreeHoleAudit
import Raw42RAUnary
import Raw42RAAlternating
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw42RACuts
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit

abbrev parent : PartialMachine :=
  refine (pathEnd root 2 (path.take 3)).1 (3,true) (some ⟨false,false,1⟩)
abbrev ra : PartialMachine := refine parent (1,true) (some ⟨false,true,0⟩)
abbrev lb : PartialMachine := refine ra (0,true) (some ⟨true,false,1⟩)
abbrev le : PartialMachine := refine ra (0,true) (some ⟨true,false,4⟩)
abbrev unary : PartialMachine := refine lb (2,true) (some ⟨false,true,2⟩)
abbrev alternating : PartialMachine := refine le (4,false) (some ⟨false,false,3⟩)

theorem first_query : zipQueryOK 17 parent 6 (1,true) = true := by decide
theorem ra_query : zipQueryOK 17 ra 9 (0,true) = true := by decide
theorem lb_query : zipQueryOK 17 lb 11 (2,true) = true := by decide
theorem le_query : zipQueryOK 17 le 10 (4,false) = true := by decide

theorem unary_eq : unary = BB6.Agent32Raw42RAUnary.p := by
  apply tableOK_sound
  decide

theorem alternating_eq : alternating = BB6.Agent32Raw42RAAlternating.p := by
  apply tableOK_sound
  decide

theorem unary_cover (B : Nat) : Cover (WeightedBound B) unary := by
  refine .leaf unary ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42RAUnary.never m (unary_eq ▸ hm))

theorem alternating_cover (B : Nat) : Cover (WeightedBound B) alternating := by
  refine .leaf alternating ?_
  intro m hm
  exact weighted_never B m (BB6.Agent32Raw42RAAlternating.never m (alternating_eq ▸ hm))

#print axioms first_query
#print axioms ra_query
#print axioms lb_query
#print axioms le_query
#print axioms unary_cover
#print axioms alternating_cover
end BB6.Agent32Raw42RACuts
