import A25Raw123Data
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent25Raw123
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6Coverage.Agent10ZipAudit BB6.Agent47CanonicalFrontier BB6.Agent47CanonicalRefinement

/-- A concrete late halt in raw123. Its ordinary move count is 9108;
the final query contributes one more. -/
theorem attained123 : ∃ m, compatible p123 m ∧ HaltsAfter m 9108 ∧ 0 ∈ delays (zeroNext m) 0 := by
  let p0 := p123
  let p1 := refine p0 (0,true) (some ⟨false,false,5⟩)
  let p2 := refine p1 (1,true) (some ⟨true,true,1⟩)
  let p3 := refine p2 (2,true) (some ⟨false,true,4⟩)
  let p4 := refine p3 (5,false) (some ⟨true,false,0⟩)
  let p5 := refine p4 (5,true) (some ⟨true,true,5⟩)
  let p6 := refine p5 (4,false) none
  let m := weightedTNFDefaultCompletion p6
  have h0 : p0 (0,true) = none := by decide
  have h1 : p1 (1,true) = none := by decide
  have h2 : p2 (2,true) = none := by decide
  have h3 : p3 (5,false) = none := by decide
  have h4 : p4 (5,true) = none := by decide
  have h5 : p5 (4,false) = none := by decide
  have hr : (knownRun p5 9108).map readSlot = some (4,false) := by
    rw [← zipRead_eq]
    decide
  have hm6 : compatible p6 m := weightedTNFDefaultCompletion_compatible _
  have hm5 : compatible p5 m := refine_preserves_compat p5 m (4,false) none h5 hm6
  have hm4 : compatible p4 m := refine_preserves_compat p4 m (5,true) (some ⟨true,true,5⟩) h4 hm5
  have hm3 : compatible p3 m := refine_preserves_compat p3 m (5,false) (some ⟨true,false,0⟩) h3 hm4
  have hm2 : compatible p2 m := refine_preserves_compat p2 m (2,true) (some ⟨false,true,4⟩) h2 hm3
  have hm1 : compatible p1 m := refine_preserves_compat p1 m (1,true) (some ⟨true,true,1⟩) h1 hm2
  have hm0 : compatible p0 m := refine_preserves_compat p0 m (0,true) (some ⟨false,false,5⟩) h0 hm1
  have hd : 0 ∈ delays (zeroNext m) 0 := by decide
  refine ⟨m,hm0,?_,hd⟩
  cases hrun : knownRun p5 9108 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = (4,false) := by simpa [hrun] using hr
    apply first_hole_halts p5 9108 c hrun
    · simpa [hs] using h5
    · simpa [hs] using hm6

theorem lower123 (B : Nat) (h : ∀ m, compatible p123 m → WeightedBound B m) : 9109 ≤ B := by
  obtain ⟨m,hm,hh,hd⟩ := attained123
  have hb := h m hm 9108 0 hh hd
  omega

/-- Preserve every other quotient parent. Raw123 is replaced by the
explicit partial audit complement, at any target at least 9109. -/
theorem graft123_sound {B : Nat} {roster : List Entry}
    (hB : 9109 ≤ B)
    (hroot : ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ roster, TNFQuotientCompatible e.2 m) :
    ∀ m, compatible root m → WeightedBound B m ∨
      ∃ e ∈ graftRoster p123 residuals123 roster, TNFQuotientCompatible e.2 m := by
  apply graftRoster_sound p123_root hroot
  intro m hm
  rcases sound123 m hm with hb | hr
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) hB)
  · exact Or.inr hr

#print axioms attained123
#print axioms lower123
#print axioms graft123_sound
end BB6.Agent25Raw123
