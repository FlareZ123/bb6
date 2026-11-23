import LowM67All65Source
import LowM67D4ThirdSource

namespace BB6.Agent13Low523Source

/-- Three disjoint complete original-source valuation-six parent
    obstructions, together with the previously accepted 16/128
    two-parent low cylinders. In the common modulus 4096, these
    clauses represent 512+8+2+1 = 523 forbidden residues. -/
theorem low_stop_fivehundredtwentythree_mod4096_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : ((z%16=13 ∨ z%64=5 ∨ z%32=25 ∨
             z%128=9 ∨ z%128=21) ∨ z%512=65) ∨
           z%2048=1729 ∨ z%4096=3521)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  rcases hz with h65|h1729|h3521
  · exact BB6.Agent13Low65Source.low_stop_sixtyfive_mod512_unreachable
      z m k hm h65 hstop
  · exact BB6.Agent13D4Second.low_stop_m67_z1729_mod2048_unreachable
      z m k hm h1729 hstop
  · exact BB6.Agent13D4Third.low_stop_m67_z3521_mod4096_unreachable
      z m k hm h3521 hstop

#print axioms low_stop_fivehundredtwentythree_mod4096_unreachable
end BB6.Agent13Low523Source
