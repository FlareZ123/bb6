import SheepEvenSourceAlgebra
import SpecialSourceNoPower

namespace Agent17SheepPowerSource

theorem special_edge_no_power (x j : Nat)
    (h : SheepEvenInverseAlgebra.SpecialEdge x (2^j)) : False := by
  rcases h with ⟨a, h, u, ha, hu, hx, hz, hy⟩
  have hf : 3*2^a+a+2=2^h*u := by omega
  exact Agent17SheepSpecial.special_no_even_power a h u j ha hf hu hy.symm

theorem genuine_power_parent_generic {x j : Nat}
    (hx : x % 2 = 0)
    (he : SheepEven.EvenEdge x (2^j)) :
    SheepEvenInverseAlgebra.GenericEdge x (2^j) := by
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra hx he with hg | hs
  · exact hg
  · exact False.elim (special_edge_no_power x j hs)

#print axioms special_edge_no_power
#print axioms genuine_power_parent_generic

end Agent17SheepPowerSource
