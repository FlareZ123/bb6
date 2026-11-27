import Raw139NormalizedE0TenNativeBounds
import ChampionScoreLowerBound

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0TenChampion

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
open BB6.Agent14Raw139NormalizedE0TenNativeBounds

/-- This is the actual first-blank-delay adjusted score of the separately
    source-certified six-state champion, not a made-up cutoff. -/
abbrev championB : Nat := BB6Coverage.Agent48DirectRoot.proposedTM63Moves + 7

/-- The accepted E0=1LB parent has the largest of these ten native bounds,
    and even it is far below the exact source champion score. -/
theorem championB_ge_ten_native : 187672026 ≤ championB :=
  Nat.le_trans
    (by decide : 187672026 ≤ 2^63)
    BB6.Agent38ChampionThreshold.champion_score_ge_pow63

/-- Original Raw139 p0 at the *actual champion cutoff*, conditional only
    on 57 unclassified normalized tables plus the other original sibling and
    continuation obligations. The ten E0 Covers are supplied at native
    independently source-certified bounds, not lifted by an assumed axiom. -/
theorem raw139_p0_at_champion_from_57
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound championB) (child r.1 r.2))
    (h57 : ∀ p ∈ normalizedAfterTen, Cover (WeightedBound championB) p)
    (hrc : Cover (WeightedBound championB) (leaf rowRC) →
      Cover (WeightedBound championB) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound championB) (leaf rowRE) →
      Cover (WeightedBound championB) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound championB) p7) :
    Cover (WeightedBound championB) p0 :=
  raw139_p0_from_57_native championB championB_ge_ten_native
    hSix hRF hRA hLB hLD ha h57 hrc hre hf

/-- The conditional 56-table analogue additionally assumes exactly the
    known ZeroLF bound 19007; this premise is pending whole-parent acceptance
    and must not be regarded as automatically discharged. -/
theorem raw139_p0_at_champion_from_56
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD)
    (hZeroLF : Cover (WeightedBound 19007) e0ZeroLF)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound championB) (child r.1 r.2))
    (h56 : ∀ p ∈ normalizedAfterEleven, Cover (WeightedBound championB) p)
    (hrc : Cover (WeightedBound championB) (leaf rowRC) →
      Cover (WeightedBound championB) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound championB) (leaf rowRE) →
      Cover (WeightedBound championB) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound championB) p7) :
    Cover (WeightedBound championB) p0 :=
  raw139_p0_from_56_native championB championB_ge_ten_native
    hSix hRF hRA hLB hLD hZeroLF ha h56 hrc hre hf

#print axioms championB_ge_ten_native
#print axioms raw139_p0_at_champion_from_57
#print axioms raw139_p0_at_champion_from_56

end BB6.Agent14Raw139NormalizedE0TenChampion
