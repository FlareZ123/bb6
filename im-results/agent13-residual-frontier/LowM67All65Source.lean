import U16AllSource
import LowM67D4Source

namespace BB6.Agent13Low65Source

/-- Uniform original-source all-time exclusion for sixty-five disjoint
    z residue classes modulo 512 of the low stopping-index ray m=512z+67.
    Sixteen classes modulo128 are handled by a complete two-parent fan,
    while z=65 modulo512 requires the complete three-parent valuation-six
    fan. The conclusion is a necessary low-gateway obstruction, not a
    complete Machine C or BB(6) decision. -/
theorem low_stop_sixtyfive_mod512_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : (z%16=13 ∨ z%64=5 ∨ z%32=25 ∨
           z%128=9 ∨ z%128=21) ∨ z%512=65)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  rcases hz with h16|h65
  · exact BB6.Agent13LowM67Sixteen.low_stop_sixteen_mod128_unreachable
      z m k hm h16 hstop
  · exact BB6.Agent13D4Low.low_stop_m67_z65_mod512_unreachable
      z m k hm h65 hstop

#print axioms low_stop_sixtyfive_mod512_unreachable
end BB6.Agent13Low65Source
