import SectionAllInverse
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3Y3X256Counterexample
open BB6.Agent46

/-- Concrete second source parent refuting the claimed unique-parent
    classification for x=10 mod 256. -/
theorem x266_second_parent :
    secNext (31,115)=some (266,3) := by
  apply (section_preimage_all_iff 31 115 266 3).mpr
  norm_num [sectionPreimageAll]

#print axioms x266_second_parent
end BB6.Agent3Y3X256Counterexample
