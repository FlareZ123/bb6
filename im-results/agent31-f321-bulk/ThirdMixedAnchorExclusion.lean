import FirstMixedAnchorExclusion
import HighFarRootTargets
import Lean.Elab.Tactic.Omega

/-!
Exact root exclusion for the third member of the dangerous
H^(24k+22)/Far terminal-suffix family (k=2).

The relevant MiddleOdd predecessor has first counter
1,349,247,566,534,184,346,750. Strict sum growth confines any such root
occurrence to steps 4738..4950. Inside that finite band, executable/source
completeness reduces the claim to a kernel-decided list of 213 first counters.
-/

set_option maxRecDepth 300000

namespace BB6.Agent31F321ThirdMixed
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent31F321HighFarRootTargets

theorem root_at_4737 :
    CounterReach 1 1 4737
      682322959708132546308
      1101711206989331108059 :=
  rootIter_sound (by decide)

theorem root_at_4738 :
    CounterReach 1 1 4738
      2729291838832530185238 1 :=
  rootIter_sound (by decide)

theorem root_at_4951 :
    CounterReach 1 1 4951
      5602848659246118512566 1 :=
  rootIter_sound (by decide)

def thirdWindowFirsts : List (Option Nat) :=
  (List.range 213).map fun j =>
    (rootIter j 2729291838832530185238 1).map Prod.fst

theorem third_target_not_in_window :
    some 1349247566534184346750 ∉ thirdWindowFirsts := by
  decide

theorem root_sum_before_4738
    {n A D : Nat}
    (hn : n≤4737)
    (hr : CounterReach 1 1 n A D) :
    A+D ≤ 1784034166697463654367 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have h4737 :
      CounterReach 1 1 (n+m)
        682322959708132546308
        1101711206989331108059 := by
    simpa [←hm] using root_at_4737
  rcases counterReach_split h4737 with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hr hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem root_sum_after_4950
    {n A D : Nat}
    (hn : 4951≤n)
    (hr : CounterReach 1 1 n A D) :
    5602848659246118512567 ≤ A+D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_4951 hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem third_window_first_not_target
    {n A D : Nat}
    (hlo : 4738≤n)
    (hhi : n≤4950)
    (hr : CounterReach 1 1 n A D) :
    A ≠ 1349247566534184346750 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j<213 := by omega
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_4738 hpre with ⟨rfl,rfl⟩
  have hcomp := rootIter_complete htail
  intro hA
  subst A
  have hmem : some 1349247566534184346750 ∈ thirdWindowFirsts := by
    unfold thirdWindowFirsts
    apply List.mem_map.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    rw [hcomp]
    rfl
  exact third_target_not_in_window hmem

theorem third_mixed_anchor_middleOdd_predecessor_unreachable
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hR : 4*a+6=5396990266136737387006)
    (h1 : a<d)
    (h2 : d<3*a+1) :
    False := by
  have ha : a=1349247566534184346750 := by omega
  subst a
  by_cases hEarly : n≤4737
  · have hs := root_sum_before_4738 hEarly hr
    omega
  by_cases hLate : 4951≤n
  · have hs := root_sum_after_4950 hLate hr
    omega
  exact (third_window_first_not_target (by omega) (by omega) hr) rfl

theorem dangerR_two :
    dangerR 2 = 5396990266136737387006 := by
  decide

/-- The k=2 source-faithful H^70/F terminal anchor is absent from the
    authentic root small-anchor orbit. -/
theorem third_danger_anchor_not_root
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR 2) 1) :
    False := by
  have hm := danger_anchor_requires_middleOdd hr ha
  rw [dangerR_two] at hm
  exact third_mixed_anchor_middleOdd_predecessor_unreachable
    hr hm.2.2.2 hm.1 hm.2.1

#print axioms root_at_4737
#print axioms root_at_4738
#print axioms root_at_4951
#print axioms third_target_not_in_window
#print axioms third_mixed_anchor_middleOdd_predecessor_unreachable
#print axioms third_danger_anchor_not_root
end BB6.Agent31F321ThirdMixed
