import FirstMixedAnchorExclusion
import HighFarRootTargets
import Lean.Elab.Tactic.Omega

/-!
Exact root exclusion for the sixth member of the dangerous
H^(24k+22)/Far terminal-suffix family (k=5).
-/

set_option maxRecDepth 700000

namespace BB6.Agent31F321SixthMixed
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent31F321HighFarRootTargets

theorem root_at_17870 :
    CounterReach 1 1 17870
      5376770906055488929299757765333181143951379
      6968982874540819731729911960202612970618877 :=
  rootIter_sound (by decide)

theorem root_at_17871 :
    CounterReach 1 1 17871
      21507083624221955717199031061332724575805522 2 :=
  rootIter_sound (by decide)

theorem root_at_18013 :
    CounterReach 1 1 18013
      30276471500561265014956828563709994538271638 1 :=
  rootIter_sound (by decide)

def sixthWindowFirsts : List (Option Nat) :=
  (List.range 142).map fun j =>
    (rootIter j 21507083624221955717199031061332724575805522 2).map Prod.fst

theorem sixth_target_not_in_window :
    some 6371641485294463754724490935042389001708652 ∉ sixthWindowFirsts := by
  decide

theorem root_sum_before_17871
    {n A D : Nat}
    (hn : n≤17870)
    (hr : CounterReach 1 1 n A D) :
    A+D ≤ 12345753780596308661029669725535794114570256 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have h17870 :
      CounterReach 1 1 (n+m)
        5376770906055488929299757765333181143951379
        6968982874540819731729911960202612970618877 := by
    simpa [←hm] using root_at_17870
  rcases counterReach_split h17870 with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hr hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem root_sum_after_18012
    {n A D : Nat}
    (hn : 18013≤n)
    (hr : CounterReach 1 1 n A D) :
    30276471500561265014956828563709994538271639 ≤ A+D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_18013 hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem sixth_window_first_not_target
    {n A D : Nat}
    (hlo : 17871≤n)
    (hhi : n≤18012)
    (hr : CounterReach 1 1 n A D) :
    A ≠ 6371641485294463754724490935042389001708652 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j<142 := by omega
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_17871 hpre with ⟨rfl,rfl⟩
  have hcomp := rootIter_complete htail
  intro hA
  subst A
  have hmem : some 6371641485294463754724490935042389001708652 ∈ sixthWindowFirsts := by
    unfold sixthWindowFirsts
    apply List.mem_map.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    rw [hcomp]
    rfl
  exact sixth_target_not_in_window hmem

theorem sixth_mixed_anchor_middleOdd_predecessor_unreachable
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hR : 4*a+6=25486565941177855018897963740169556006834614)
    (h1 : a<d)
    (h2 : d<3*a+1) :
    False := by
  have ha : a=6371641485294463754724490935042389001708652 := by omega
  subst a
  by_cases hEarly : n≤17870
  · have hs := root_sum_before_17871 hEarly hr
    omega
  by_cases hLate : 18013≤n
  · have hs := root_sum_after_18012 hLate hr
    omega
  exact (sixth_window_first_not_target (by omega) (by omega) hr) rfl

theorem dangerR_five :
    dangerR 5 = 25486565941177855018897963740169556006834614 := by
  decide

theorem sixth_danger_anchor_not_root
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR 5) 1) :
    False := by
  have hm := danger_anchor_requires_middleOdd hr ha
  rw [dangerR_five] at hm
  exact sixth_mixed_anchor_middleOdd_predecessor_unreachable
    hr hm.2.2.2 hm.1 hm.2.1

#print axioms root_at_17870
#print axioms root_at_17871
#print axioms root_at_18013
#print axioms sixth_target_not_in_window
#print axioms sixth_mixed_anchor_middleOdd_predecessor_unreachable
#print axioms sixth_danger_anchor_not_root
end BB6.Agent31F321SixthMixed
