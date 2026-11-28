import FirstMixedAnchorExclusion
import HighFarRootTargets
import Lean.Elab.Tactic.Omega

/-!
Exact root exclusion for the fifth member of the dangerous
H^(24k+22)/Far terminal-suffix family (k=4).

Strict sum growth confines the unique MiddleOdd predecessor first counter to
steps 12647..12882. Executable/source completeness reduces the remaining
236-step band to a kernel-decided list.
-/

set_option maxRecDepth 500000

namespace BB6.Agent31F321FifthMixed
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent31F321HighFarRootTargets

theorem root_at_12646 :
    CounterReach 1 1 12646
      243458569558552429774413788054311310
      332306998946228968225951765070086141 :=
  rootIter_sound (by decide)

theorem root_at_12647 :
    CounterReach 1 1 12647
      973834278234209719097655152217245246 1 :=
  rootIter_sound (by decide)

theorem root_at_12883 :
    CounterReach 1 1 12883
      1624454496005738840072508302532308342 1 :=
  rootIter_sound (by decide)

def fifthWindowFirsts : List (Option Nat) :=
  (List.range 236).map fun j =>
    (rootIter j 973834278234209719097655152217245246 1).map Prod.fst

theorem fifth_target_not_in_window :
    some 379779427367118820829659160080098418 ∉ fifthWindowFirsts := by
  decide

theorem root_sum_before_12647
    {n A D : Nat}
    (hn : n≤12646)
    (hr : CounterReach 1 1 n A D) :
    A+D ≤ 575765568504781398000365553124397451 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have h12646 :
      CounterReach 1 1 (n+m)
        243458569558552429774413788054311310
        332306998946228968225951765070086141 := by
    simpa [←hm] using root_at_12646
  rcases counterReach_split h12646 with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hr hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem root_sum_after_12882
    {n A D : Nat}
    (hn : 12883≤n)
    (hr : CounterReach 1 1 n A D) :
    1624454496005738840072508302532308343 ≤ A+D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_12883 hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem fifth_window_first_not_target
    {n A D : Nat}
    (hlo : 12647≤n)
    (hhi : n≤12882)
    (hr : CounterReach 1 1 n A D) :
    A ≠ 379779427367118820829659160080098418 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j<236 := by omega
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_12647 hpre with ⟨rfl,rfl⟩
  have hcomp := rootIter_complete htail
  intro hA
  subst A
  have hmem : some 379779427367118820829659160080098418 ∈ fifthWindowFirsts := by
    unfold fifthWindowFirsts
    apply List.mem_map.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    rw [hcomp]
    rfl
  exact fifth_target_not_in_window hmem

theorem fifth_mixed_anchor_middleOdd_predecessor_unreachable
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hR : 4*a+6=1519117709468475283318636640320393678)
    (h1 : a<d)
    (h2 : d<3*a+1) :
    False := by
  have ha : a=379779427367118820829659160080098418 := by omega
  subst a
  by_cases hEarly : n≤12646
  · have hs := root_sum_before_12647 hEarly hr
    omega
  by_cases hLate : 12883≤n
  · have hs := root_sum_after_12882 hLate hr
    omega
  exact (fifth_window_first_not_target (by omega) (by omega) hr) rfl

theorem dangerR_four :
    dangerR 4 = 1519117709468475283318636640320393678 := by
  decide

theorem fifth_danger_anchor_not_root
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR 4) 1) :
    False := by
  have hm := danger_anchor_requires_middleOdd hr ha
  rw [dangerR_four] at hm
  exact fifth_mixed_anchor_middleOdd_predecessor_unreachable
    hr hm.2.2.2 hm.1 hm.2.1

#print axioms root_at_12646
#print axioms root_at_12647
#print axioms root_at_12883
#print axioms fifth_target_not_in_window
#print axioms fifth_mixed_anchor_middleOdd_predecessor_unreachable
#print axioms fifth_danger_anchor_not_root
end BB6.Agent31F321FifthMixed
