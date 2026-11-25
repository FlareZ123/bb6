import Raw113Data
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw113
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- The late first-hole witness contributes 2673 ordinary moves plus halt. -/
theorem attained113 : ∃ m, compatible p113 m ∧ HaltsAfter m 2673 ∧ 0 ∈ delays (zeroNext m) 0 := by
  let p0 := p113
  let p1 := refine p0 (2,true) (some ⟨false,false,5⟩)
  let p2 := refine p1 (0,true) (some ⟨false,false,0⟩)
  let p3 := refine p2 (4,false) (some ⟨false,true,2⟩)
  let p4 := refine p3 (5,false) (some ⟨false,true,1⟩)
  let p5 := refine p4 (5,true) (some ⟨true,false,0⟩)
  let p6 := refine p5 (1,true) none
  let m := weightedTNFDefaultCompletion p6
  have h0 : p0 (2,true) = none := by decide
  have h1 : p1 (0,true) = none := by decide
  have h2 : p2 (4,false) = none := by decide
  have h3 : p3 (5,false) = none := by decide
  have h4 : p4 (5,true) = none := by decide
  have h5 : p5 (1,true) = none := by decide
  have hr : (knownRun p5 2673).map readSlot = some (1,true) := by
    rw [← zipRead_eq]
    decide
  have hm6 : compatible p6 m := weightedTNFDefaultCompletion_compatible _
  have hm5 : compatible p5 m := refine_preserves_compat p5 m (1,true) none h5 hm6
  have hm4 : compatible p4 m := refine_preserves_compat p4 m (5,true) (some ⟨true,false,0⟩) h4 hm5
  have hm3 : compatible p3 m := refine_preserves_compat p3 m (5,false) (some ⟨false,true,1⟩) h3 hm4
  have hm2 : compatible p2 m := refine_preserves_compat p2 m (4,false) (some ⟨false,true,2⟩) h2 hm3
  have hm1 : compatible p1 m := refine_preserves_compat p1 m (0,true) (some ⟨false,false,0⟩) h1 hm2
  have hm0 : compatible p0 m := refine_preserves_compat p0 m (2,true) (some ⟨false,false,5⟩) h0 hm1
  have hd : 0 ∈ delays (zeroNext m) 0 := by decide
  refine ⟨m,hm0,?_,hd⟩
  cases hrun : knownRun p5 2673 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (1,true) := by simpa [hrun] using hr
    apply first_hole_halts p5 2673 c hrun
    · simpa [hs] using h5
    · simpa [hs] using hm6

theorem exact113 (T : Nat) :
    (∀ m, compatible p113 m → WeightedBound T m) ↔ 2674 ≤ T := by
  constructor
  · intro h
    obtain ⟨m,hm,hh,hd⟩ := attained113
    have hb := h m hm 2673 0 hh hd
    omega
  · intro hb m hm k d hk hd
    exact Nat.le_trans (all113 m hm k d hk hd) hb

/-- Consume the concrete parent certificate in any current quotient roster,
    including future versions. All other parents are preserved by graftRoster. -/
theorem graft113_sound {B : Nat} {roster : List Entry}
    (hB : 2674 ≤ B)
    (hroot : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ graftRoster p113 [] roster, TNFQuotientCompatible e.2 m :=
  graftRoster_sound p113_root hroot
    (fun m hm => Or.inl ((exact113 B).mpr hB m hm))

#print axioms attained113
#print axioms exact113
#print axioms graft113_sound
end BB6.Agent25Raw113
