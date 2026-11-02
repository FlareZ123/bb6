import M8M16Composition
import M32HighSourceBridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent43

/-- Source-linked genuine blank-origin section exclusion under the exact
    low stopping equation, subject to original M32 kernel closure theorem. -/
theorem blank_no_low_m32_24 (m k : Nat)
    (hm : m%32=24)
    (heq : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent15.CReach 1 k := by
  intro hr
  exact CCert.original_low_parameter_24_absent m k
    (by omega) hm heq (BB6.Agent15.section_reach_embeds hr)

/-- Source-linked genuine blank-origin section exclusion for 24 high
    stopping-parameter residue pairs, m>=2. -/
theorem blank_no_high_m32_pairs (j m k : Nat)
    (hm : 2≤m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp : (j%32,m%32) ∈ CCert.newHighPairs) :
    ¬ BB6.Agent15.CReach (2*j+3) k := by
  intro hr
  exact CCert.original_high_24_pairs_all_j_unreachable j m k hm heq hp
    (BB6.Agent15.section_reach_embeds hr)

#print axioms blank_no_low_m32_24
#print axioms blank_no_high_m32_pairs
end BB6.Agent43
