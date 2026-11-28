import FirstMixedAnchorExclusion
import HighFarRootTargets
import Lean.Elab.Tactic.Omega

/-!
Exact root exclusion for the fourth member of the dangerous
H^(24k+22)/Far terminal-suffix family (k=3).

Strict sum growth confines the unique MiddleOdd predecessor first counter to
steps 7967..8066. Executable/source completeness reduces the remaining
100-step band to a kernel-decided list.
-/

set_option maxRecDepth 400000

namespace BB6.Agent31F321FourthMixed
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent31F321HighFarRootTargets

theorem root_at_7966 :
    CounterReach 1 1 7966
      14551590149244121689456647355
      24758800785707605497982484477 :=
  rootIter_sound (by decide)

theorem root_at_7967 :
    CounterReach 1 1 7967
      58206360596976486757826589426 2 :=
  rootIter_sound (by decide)

theorem root_at_8067 :
    CounterReach 1 1 8067
      99844862868640785913315701390 2 :=
  rootIter_sound (by decide)

def fourthWindowFirsts : List (Option Nat) :=
  (List.range 100).map fun j =>
    (rootIter j 58206360596976486757826589426 2).map Prod.fst

theorem fourth_target_not_in_window :
    some 22636617861218382169583985784 ∉ fourthWindowFirsts := by
  decide

theorem root_sum_before_7967
    {n A D : Nat}
    (hn : n≤7966)
    (hr : CounterReach 1 1 n A D) :
    A+D ≤ 39310390934951727187439131832 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have h7966 :
      CounterReach 1 1 (n+m)
        14551590149244121689456647355
        24758800785707605497982484477 := by
    simpa [←hm] using root_at_7966
  rcases counterReach_split h7966 with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hr hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem root_sum_after_8066
    {n A D : Nat}
    (hn : 8067≤n)
    (hr : CounterReach 1 1 n A D) :
    99844862868640785913315701392 ≤ A+D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_8067 hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem fourth_window_first_not_target
    {n A D : Nat}
    (hlo : 7967≤n)
    (hhi : n≤8066)
    (hr : CounterReach 1 1 n A D) :
    A ≠ 22636617861218382169583985784 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j<100 := by omega
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_7967 hpre with ⟨rfl,rfl⟩
  have hcomp := rootIter_complete htail
  intro hA
  subst A
  have hmem : some 22636617861218382169583985784 ∈ fourthWindowFirsts := by
    unfold fourthWindowFirsts
    apply List.mem_map.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    rw [hcomp]
    rfl
  exact fourth_target_not_in_window hmem

theorem fourth_mixed_anchor_middleOdd_predecessor_unreachable
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hR : 4*a+6=90546471444873528678335943142)
    (h1 : a<d)
    (h2 : d<3*a+1) :
    False := by
  have ha : a=22636617861218382169583985784 := by omega
  subst a
  by_cases hEarly : n≤7966
  · have hs := root_sum_before_7967 hEarly hr
    omega
  by_cases hLate : 8067≤n
  · have hs := root_sum_after_8066 hLate hr
    omega
  exact (fourth_window_first_not_target (by omega) (by omega) hr) rfl

theorem dangerR_three :
    dangerR 3 = 90546471444873528678335943142 := by
  decide

theorem fourth_danger_anchor_not_root
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR 3) 1) :
    False := by
  have hm := danger_anchor_requires_middleOdd hr ha
  rw [dangerR_three] at hm
  exact fourth_mixed_anchor_middleOdd_predecessor_unreachable
    hr hm.2.2.2 hm.1 hm.2.1

#print axioms root_at_7966
#print axioms root_at_7967
#print axioms root_at_8067
#print axioms fourth_target_not_in_window
#print axioms fourth_mixed_anchor_middleOdd_predecessor_unreachable
#print axioms fourth_danger_anchor_not_root
end BB6.Agent31F321FourthMixed
