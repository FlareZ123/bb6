import CSourceBridge8
set_option maxRecDepth 16384

namespace CCert

-- The entire two-parameter congruence cylinder avoids the
-- fully kernel-certified abstract blank-entry orbit.
theorem seven_four_abstract_exclusion (u v : Nat) :
    seen (q (8*u+7)) (q (8*v+4)) (q 0) = false := by
  rcases u with _ | u
  · rcases v with _ | v
    · decide
    · have hk : q (8*(v+1)+4) = q 12 :=
        q_congr_big _ _ (by omega) (by omega) (by omega)
      rw [hk]
      decide
  · have ha : q (8*(u+1)+7) = q 15 :=
      q_congr_big _ _ (by omega) (by omega) (by omega)
    rw [ha]
    rcases v with _ | v
    · decide
    · have hk : q (8*(v+1)+4) = q 12 :=
        q_congr_big _ _ (by omega) (by omega) (by omega)
      rw [hk]
      decide

-- This Reach is the exact original published Machine C accelerator,
-- rather than merely an independently copied finite simulation.
theorem published_no_seven_four (u v : Nat) :
    ¬ BB6CLine.Reach (8*u+7, 8*v+4, 0) := by
  intro h
  have hs := reachable_seen (source_reachable_embeds h)
  have hfalse := seven_four_abstract_exclusion u v
  rw [hfalse] at hs
  cases hs

#print axioms seven_four_abstract_exclusion
#print axioms published_no_seven_four
end CCert
