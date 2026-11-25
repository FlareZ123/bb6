import Raw120Late
import Raw120Late1341

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent3Raw120ExactLower
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent3Raw120
open BB6.Agent10ZipAudit BB6.Agent31ThreeHole

abbrev q1 := refine p120 (4,false) (some ⟨true,false,1⟩)
abbrev q2 := refine q1 (1,true) (some ⟨false,false,5⟩)
abbrev q3 := refine q2 (2,true) (some ⟨false,true,5⟩)
abbrev q4 := refine q3 (5,false) (some ⟨false,true,0⟩)
abbrev q5 := refine q4 (5,true) (some ⟨false,false,4⟩)

theorem late1341_table : q5 = BB6.Agent13Raw120Late1341.table :=
  tableOK_sound _ _ (by decide)

theorem late1341_parent_compat (m : Machine)
    (hm : compatible BB6.Agent13Raw120Late1341.table m) : compatible p120 m := by
  have h5 : compatible q5 m := by rw [late1341_table]; exact hm
  have h4 : compatible q4 m := refine_preserves_compat _ _ _ _ (by decide) h5
  have h3 : compatible q3 m := refine_preserves_compat _ _ _ _ (by decide) h4
  have h2 : compatible q2 m := refine_preserves_compat _ _ _ _ (by decide) h3
  have h1 : compatible q1 m := refine_preserves_compat _ _ _ _ (by decide) h2
  exact refine_preserves_compat _ _ _ _ (by decide) h1

/-- The entire raw120 parent cannot have a uniform weighted bound below
    the exact late halter in its E0=1LB child. -/
theorem raw120_lower (B : Nat)
    (h : ∀ m, compatible p120 m → WeightedBound B m) : 224707 ≤ B :=
  (BB6.Agent13Raw120Late1341.exact_weighted B).mp
    (fun m hm => h m (late1341_parent_compat m hm))

#print axioms raw120_lower
end BB6.Agent3Raw120ExactLower
