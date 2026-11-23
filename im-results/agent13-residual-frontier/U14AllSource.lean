import U17Source
import U97U41Source
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13LowM67All

/-- Kernel-checkable original-source low-stop exclusion for fourteen
    disjoint residue classes modulo 128 of m=512*z+67:
    z=13 mod16 (eight classes), z=5 mod64 (two classes), or
    z=25 mod32 (four classes). This is all-time and requires no
    M16/M32 quotient certificate. -/
theorem low_stop_fourteen_mod128_unreachable
    (z m k : Nat) (hm : m=512*z+67)
    (hz : z%16=13 ∨ z%64=5 ∨ z%32=25)
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  rcases hz with h13|h5|h25
  · exact BB6.Agent13U17.low_stop_m67_z13_mod16_unreachable
      z m k hm h13 hstop
  · exact BB6.Agent13U97U41.low_stop_m67_z5_mod64_unreachable
      z m k hm h5 hstop
  · exact BB6.Agent13U97U41.low_stop_m67_z25_mod32_unreachable
      z m k hm h25 hstop

#print axioms low_stop_fourteen_mod128_unreachable
end BB6.Agent13LowM67All
