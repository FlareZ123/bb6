import RootMod128ThreeSource
import RootMod128FourSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New

/-- The right-counter lower threshold in blank_no_three_link follows
from the two congruences themselves; thus the entire unbounded
two-dimensional congruence cylinder is unreachable. -/
theorem blank_no_three_mod_only (x y : Nat)
    (hx : x%64=37) (hs : (x+y+1)%128=96) :
    ¬ BB6.Agent3.CReach x y :=
  blank_no_three_link x y hx hs (by omega)

/-- The corresponding fourth-link right-counter threshold is automatic
from its stronger dyadic congruences. -/
theorem blank_no_four_mod_only (x y : Nat)
    (hx : x%128=117) (hs : (x+y+1)%128=96) :
    ¬ BB6.Agent3.CReach x y :=
  blank_no_four_link x y hx hs (by omega)

#print axioms blank_no_three_mod_only
#print axioms blank_no_four_mod_only
end BB6.Agent29New
