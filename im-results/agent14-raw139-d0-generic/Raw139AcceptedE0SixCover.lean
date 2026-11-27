import Raw139NormalizedE0CutsFinite
import A3E0RACover
import Raw139E0ZeroRECover
import Raw139E0ZeroRBCover
import Raw139E0ZeroRDCover
import E0ZeroRFCover
import E0OneRECover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139AcceptedE0SixCover

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139NormalizedE0CutsFinite
abbrev e0Score : Nat := 6766859

theorem cover_mono {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (h : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  induction h with
  | leaf p hbound =>
      refine Cover.leaf p ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hAB
  | branch p s hu kids ih =>
      exact Cover.branch p s hu (fun t ht => ih t ht)

theorem liftWeighted {b : Nat} {p : PartialMachine}
    (hb : b ≤ e0Score)
    (h : ∀ m, compatible p m → WeightedBound b m) :
    Cover (WeightedBound e0Score) p := by
  refine Cover.leaf p ?_
  intro m hm k d hk hd
  exact Nat.le_trans (h m hm k d hk hd) hb

theorem e0ZeroRA_eq_parent :
    e0ZeroRA = BB6.Agent3E0RA.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

theorem e0ZeroRE_eq_parent :
    e0ZeroRE = BB6.Agent48Raw139E0ZeroRE.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

theorem e0ZeroRB_eq_parent :
    e0ZeroRB = BB6.Agent48Raw139E0ZeroRB.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

theorem e0ZeroRD_eq_parent :
    e0ZeroRD = BB6.Agent48Raw139E0ZeroRD.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

theorem e0ZeroRF_eq_parent :
    e0ZeroRF = BB6.Agent6E0ZeroRF.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

theorem e0OneRE_eq_parent :
    e0OneRE = BB6.Agent6E0OneRE.parent := by
  exact BB6.Agent14Raw139Core.sameTable_sound (by decide)

theorem e0ZeroRA_cover :
    Cover (WeightedBound e0Score) e0ZeroRA := by
  rw [e0ZeroRA_eq_parent]
  exact cover_mono
    (by decide)
    BB6.Agent3E0RA.cover

theorem e0ZeroRE_cover :
    Cover (WeightedBound e0Score) e0ZeroRE := by
  rw [e0ZeroRE_eq_parent]
  exact liftWeighted
    (by decide)
    BB6.Agent48Raw139E0ZeroRE.all_completions_weighted

theorem e0ZeroRB_cover :
    Cover (WeightedBound e0Score) e0ZeroRB := by
  rw [e0ZeroRB_eq_parent]
  exact liftWeighted
    (by decide)
    BB6.Agent48Raw139E0ZeroRB.all_completions_weighted

theorem e0ZeroRD_cover :
    Cover (WeightedBound e0Score) e0ZeroRD := by
  rw [e0ZeroRD_eq_parent]
  exact liftWeighted
    (by decide)
    BB6.Agent48Raw139E0ZeroRD.all_completions_weighted

theorem e0ZeroRF_cover :
    Cover (WeightedBound e0Score) e0ZeroRF := by
  rw [e0ZeroRF_eq_parent]
  exact cover_mono
    (by decide)
    BB6.Agent6E0ZeroRF.weighted

theorem e0OneRE_cover :
    Cover (WeightedBound e0Score) e0OneRE := by
  rw [e0OneRE_eq_parent]
  exact cover_mono
    (by decide)
    BB6.Agent6E0OneRE.weighted

theorem acceptedE0Six_cover :
    ∀ q ∈ acceptedE0Six, Cover (WeightedBound e0Score) q := by
  intro q hq
  simp only [acceptedE0Six, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact e0ZeroRA_cover
  · exact e0ZeroRE_cover
  · exact e0ZeroRB_cover
  · exact e0ZeroRD_cover
  · exact e0ZeroRF_cover
  · exact e0OneRE_cover

#print axioms e0Score
#print axioms e0ZeroRA_eq_parent
#print axioms e0ZeroRE_eq_parent
#print axioms e0ZeroRB_eq_parent
#print axioms e0ZeroRD_eq_parent
#print axioms e0ZeroRF_eq_parent
#print axioms e0OneRE_eq_parent
#print axioms acceptedE0Six_cover

end BB6.Agent14Raw139AcceptedE0SixCover
