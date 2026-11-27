import Raw139NormalizedE0TenAcceptedConditional

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedE0TenNativeBounds

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent14Raw139NormalizedE0CutsFinite
open BB6.Agent14Raw139NormalizedE0OneRFFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedFinite
open BB6.Agent14Raw139NormalizedE0TenAcceptedConditional

/-- Native parent bounds can be lifted to a single larger cutoff without
    changing the original halting/first-blank-delay semantics. -/
theorem mono_cover {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  cases h with
  | leaf _ hbound =>
      refine Cover.leaf _ ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hAB

/-- The first ten E0 parents were each accepted at a *different* exact
    primitive weighted bound: six at 6766859, then 1RF at 6024,
    1RA at 529714, 1LB at 187672026, and 1LD at 29607414.
    No parameterized halting theorem is silently assumed. -/
theorem native_ten_to_B (B : Nat) (hb : 187672026 ≤ B)
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD) :
    ∀ q ∈ acceptedE0Ten, Cover (WeightedBound B) q := by
  intro q hq
  simp only [acceptedE0Ten, List.mem_append] at hq
  rcases hq with hnew | hold
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hnew
    rcases hnew with rfl | rfl | rfl
    · exact mono_cover (Nat.le_trans (by decide : 529714 ≤ 187672026) hb) hRA
    · exact mono_cover hb hLB
    · exact mono_cover (Nat.le_trans (by decide : 29607414 ≤ 187672026) hb) hLD
  · simp only [acceptedSixPlusOneRF, List.mem_cons] at hold
    rcases hold with rfl | hsix
    · exact mono_cover (Nat.le_trans (by decide : 6024 ≤ 187672026) hb) hRF
    · exact mono_cover
        (Nat.le_trans (by decide : 6766859 ≤ 187672026) hb)
        (hSix q hsix)

/-- Native score assumptions for exactly ten original-source accepted E0
    parents plus the 57 normalized residuals and all other unchanged Raw139
    spine premises yield the p0 parent Cover for every B≥187672026. -/
theorem raw139_p0_from_57_native (B : Nat)
    (hb : 187672026 ≤ B)
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (h57 : ∀ p ∈ normalizedAfterTen, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 :=
  raw139_p0_cover_from_57 B
    (Nat.le_trans (by decide : 59 ≤ 187672026) hb)
    ha (native_ten_to_B B hb hSix hRF hRA hLB hLD) h57 hrc hre hf

/-- The prospective eleventh parent ZeroLF has exact source target 19007;
    retaining this premise produces the 56-case native-score interface. -/
theorem raw139_p0_from_56_native (B : Nat)
    (hb : 187672026 ≤ B)
    (hSix : ∀ q ∈ acceptedE0Six, Cover (WeightedBound 6766859) q)
    (hRF : Cover (WeightedBound 6024) e0OneRF)
    (hRA : Cover (WeightedBound 529714) e0OneRA)
    (hLB : Cover (WeightedBound 187672026) e0OneLB)
    (hLD : Cover (WeightedBound 29607414) e0OneLD)
    (hZeroLF : Cover (WeightedBound 19007) e0ZeroLF)
    (ha : ∀ r ∈ acceptedRows, Cover (WeightedBound B) (child r.1 r.2))
    (h56 : ∀ p ∈ normalizedAfterEleven, Cover (WeightedBound B) p)
    (hrc : Cover (WeightedBound B) (leaf rowRC) →
      Cover (WeightedBound B) (child rowRC.1 rowRC.2))
    (hre : Cover (WeightedBound B) (leaf rowRE) →
      Cover (WeightedBound B) (child rowRE.1 rowRE.2))
    (hf : Cover (WeightedBound B) p7) :
    Cover (WeightedBound B) p0 := by
  have h11 : ∀ q ∈ acceptedE0Eleven, Cover (WeightedBound B) q := by
    intro q hq
    simp only [acceptedE0Eleven, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact mono_cover (Nat.le_trans (by decide : 19007 ≤ 187672026) hb) hZeroLF
    · exact native_ten_to_B B hb hSix hRF hRA hLB hLD q hq
  exact raw139_p0_cover_from_56 B
    (Nat.le_trans (by decide : 59 ≤ 187672026) hb)
    ha h11 h56 hrc hre hf

#print axioms mono_cover
#print axioms native_ten_to_B
#print axioms raw139_p0_from_57_native
#print axioms raw139_p0_from_56_native

end BB6.Agent14Raw139NormalizedE0TenNativeBounds
