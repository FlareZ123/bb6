import M32HighSmall
import CSourceBridge32
namespace CCert

/-- Original source root: 24 full congruence families of high stopping inputs,
    restricted to j>=3, m>=2. The machine remains undecided. -/
theorem original_high_24_pairs_unreachable (j m k : Nat)
    (hj : 3 ≤ j) (hm : 2 ≤ m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp : (j%32,m%32) ∈ newHighPairs) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  exact high_24_pairs_unreachable j m k hj hm heq hp
    (source_reachable_embeds32 h)

#print axioms original_high_24_pairs_unreachable

/-- All 24 high stopping-parameter congruence families, including small j. -/
theorem original_high_24_pairs_all_j_unreachable (j m k : Nat)
    (hm : 2 ≤ m)
    (heq : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hp : (j%32,m%32) ∈ newHighPairs) :
    ¬ BB6CLine.Reach (2*j+3,k,0) := by
  intro h
  exact high_24_pairs_unreachable_all_j j m k hm heq hp
    (source_reachable_embeds32 h)

#print axioms original_high_24_pairs_all_j_unreachable
end CCert
