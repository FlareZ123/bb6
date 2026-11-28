import PostBasin
import RootCore

namespace F197.Agent2Self
open Agent2Counter

/-- An infinite parametrized live family *before* the giant generic marker
    epoch. Every valid aligned rope may be appended, and any exponent k>=45
    suffices; there is no bound above. The theorem is a genuine all-time
    statement about the original six-state transition semantics. -/
theorem generic_odd_basin_live (k : Nat) (Y : Word) (r : Rope)
    (hk : 45 ≤ k) (hr : ropeOK r = true) (hY : okHead Y = true) :
    ∀ t, run t (rstate (2*(2*k+2)+1) (M++GS++Y) r) ≠ none := by
  let tail : Tape := ropeTape ((GT++Y,1)::r)
  have htail : tail 0 = true := by
    change (pre (GT++Y) (ropeTape r)) 0 = true
    exact pre_first (GT++Y) (ropeTape r) (by decide) (rope_head r hr)
  have he :
      rstate 0 OUT ((LB,k)::(GT++Y,1)::r) = state 0 OUT (rep LB k tail) := by
    rfl
  have hb :
      ∀ t, run t (rstate 0 OUT ((LB,k)::(GT++Y,1)::r)) ≠ none := by
    rw [he]
    exact post_basin_live k tail hk htail
  exact nohalt_of_reach (root_generic11 k Y r hr hY) hb

#print axioms generic_odd_basin_live
end F197.Agent2Self
