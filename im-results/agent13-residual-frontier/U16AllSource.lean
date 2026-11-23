import U14AllSource
import U201U129Source

namespace BB6.Agent13LowM67Sixteen

/-- Source-checked all-time nonreachability in sixteen disjoint z-residue
    classes modulo 128 of the low stop m=512*z+67. Exact original-section
    transitions only; no finite-time truncation or quotient certification. -/
theorem low_stop_sixteen_mod128_unreachable
    (z m k : Nat)
    (hm : m=512*z+67)
    (hz : z%16=13 ∨ z%64=5 ∨ z%32=25 ∨
          z%128=9 ∨ z%128=21)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  rcases hz with h13|h5|h25|h9|h21
  · exact BB6.Agent13U17.low_stop_m67_z13_mod16_unreachable
      z m k hm h13 hstop
  · exact BB6.Agent13U97U41.low_stop_m67_z5_mod64_unreachable
      z m k hm h5 hstop
  · exact BB6.Agent13U97U41.low_stop_m67_z25_mod32_unreachable
      z m k hm h25 hstop
  · exact BB6.Agent13U201U129.low_stop_m67_z9_mod128_unreachable
      z m k hm h9 hstop
  · exact BB6.Agent13U201U129.low_stop_m67_z21_mod128_unreachable
      z m k hm h21 hstop

#print axioms low_stop_sixteen_mod128_unreachable
end BB6.Agent13LowM67Sixteen
