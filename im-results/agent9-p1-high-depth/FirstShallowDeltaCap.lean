import Lean
open Lean

namespace BB6.Agent9FirstShallowCoordinateGate

/--
The immediate first-shallow terminal wall in the Is=20 branch is impossible
for either positive slack delta=1 or delta=2. This version uses the existing
terminal cost-one cap, so it does not depend on the delta=2-only defect
coefficient 18P.
-/
theorem is20_immediate_terminal_impossible_with_cap
    (P n M u delta : Nat)
    (hn : 83 ≤ n)
    (hPbig : 2*n ≤ P)
    (hdelta : 1 ≤ delta ∧ delta ≤ 2)
    (hOffset : M+n+delta+1=14*u)
    (hWall : 22*u+4=3*P)
    (hcap : 128*(M+3)<93*P) : False := by
  omega

#print axioms is20_immediate_terminal_impossible_with_cap

end BB6.Agent9FirstShallowCoordinateGate
