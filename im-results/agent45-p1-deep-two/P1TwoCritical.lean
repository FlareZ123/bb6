import P1TwoIff
import P1Gate

namespace BB6.Agent45TwoRoot
open BB6.Agent1

/-- Three exact T steps map any reachable positive critical root to its
    true reset-counter critical target, with no blank-entry assumption. -/
theorem critical_root_to_target (u : Nat) :
    Reach (8*u+4) 3 → Reach 2 (8*u+10) := by
  intro hr
  have h1 : T (8*u+4) 3 = some (8*u+7,1) := by
    have he : (8*u+4)%2=0 := by omega
    simp only [T, show (3:Nat)≠0 by decide,
      show (3:Nat)≠1 by decide,if_false,if_pos he]
  have h2 : T (8*u+7) 1 = some (8*u+9,0) := by
    simp [T]
  have h3 : T (8*u+9) 0 = some (2,8*u+10) := by
    simp [T]
  exact Reach.next _ _ _ _
    (Reach.next _ _ _ _ (Reach.next _ _ _ _ hr h1) h2) h3

/-- The n=2-sector's critical reset target is reachable iff either of the
    two genuine two-T-step feeder lines has a reachable member. -/
theorem critical_target_iff_two_feeders (u : Nat)
    (hu : u%2=1) (hge : 3≤u) :
    Reach 2 (8*u+10) ↔
      Reach (4*u-4) (4*u+9) ∨ Reach (6*u-2) (2*u+5) := by
  constructor
  · intro hr
    have hroot : Reach (8*u+4) 3 := by
      have hs := BB6.Agent50P1.critical_target_implies_three
        (8*u+10) (by omega) (by omega) hr
      simpa only [show 8*u+10-6=8*u+4 by omega] using hs
    exact (root_reach_iff_two_feeders u hu hge).mp hroot
  · intro h
    exact critical_root_to_target u
      ((root_reach_iff_two_feeders u hu hge).mpr h)

#print axioms critical_root_to_target
#print axioms critical_target_iff_two_feeders
end BB6.Agent45TwoRoot
