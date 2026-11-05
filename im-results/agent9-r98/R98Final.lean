import R98Root
import P1Gate

namespace BB6.Agent9R98
set_option maxHeartbeats 0

/-- For all q, actual P1 blank-entry T dynamics cannot visit this halting-critical reset. -/
theorem no_blank_critical_98_mod65536 (q:Nat) :
    ¬BB6.Agent1.Reach 2
      (14*2^(65536*q+98)-2*(65536*q+98)-10) := by
  let d := 14*2^(65536*q+98)-2*(65536*q+98)-10
  have he : d-6 = 131072*paramT q+130860 := by
    change (14*2^(65536*q+98)-2*(65536*q+98)-10)-6 =
      131072*paramT q+130860
    rw [Nat.sub_sub]
    simpa only [Nat.reduceAdd] using root_eq q
  have arithmetic : ∀ (d t:Nat),
      d-6=131072*t+130860 → 10≤d ∧ d%4=2 := by
    intro x t hx
    omega
  obtain ⟨hd,hm⟩ := arithmetic d (paramT q) he
  have hno : ¬BB6.Agent1.Reach (131072*paramT q+130860) 3 :=
    BB6.Agent4Cone.blocked_no_reach _ _ (root_blocked q)
  intro hr
  have hg := BB6.Agent50P1.critical_target_implies_three d hd hm hr
  exact hno (by simpa only [he] using hg)

#print axioms no_blank_critical_98_mod65536
end BB6.Agent9R98
