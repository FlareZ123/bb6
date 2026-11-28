import FirstMixedAnchorExclusion
import HighFarRootTargets
import Lean.Elab.Tactic.Omega

/-!
Exact root exclusion for the second member of the dangerous
H^(24k+22)/Far terminal-suffix family (k=1).

The relevant MiddleOdd predecessor has first counter 80,421,421,917,316.
Strict sum growth confines any such root occurrence to steps 1855..2042.
Inside that finite band, the exact executable/source equivalence reduces the
claim to a kernel-decided list of 188 first counters.
-/

set_option maxRecDepth 200000

namespace BB6.Agent31F321SecondMixed
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent31F321HighFarRootTargets

theorem root_at_1854 :
    CounterReach 1 1 1854 41714293242654 70368744177661 :=
  rootIter_sound (by decide)

theorem root_at_1855 :
    CounterReach 1 1 1855 166857172970622 1 :=
  rootIter_sound (by decide)

theorem root_at_2043 :
    CounterReach 1 1 2043 430663388763734 1 :=
  rootIter_sound (by decide)

def secondWindowFirsts : List (Option Nat) :=
  (List.range 188).map fun j =>
    (rootIter j 166857172970622 1).map Prod.fst

theorem second_target_not_in_window :
    some 80421421917316 ∉ secondWindowFirsts := by
  decide

theorem root_sum_before_1855
    {n A D : Nat}
    (hn : n≤1854)
    (hr : CounterReach 1 1 n A D) :
    A+D ≤ 112083037420315 := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hn
  have h1854 :
      CounterReach 1 1 (n+m) 41714293242654 70368744177661 := by
    simpa [←hm] using root_at_1854
  rcases counterReach_split h1854 with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hr hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem root_sum_after_2042
    {n A D : Nat}
    (hn : 2043≤n)
    (hr : CounterReach 1 1 n A D) :
    430663388763735 ≤ A+D := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_2043 hpre with ⟨rfl,rfl⟩
  have hs := counterReach_sum_mono htail
  omega

theorem second_window_first_not_target
    {n A D : Nat}
    (hlo : 1855≤n)
    (hhi : n≤2042)
    (hr : CounterReach 1 1 n A D) :
    A ≠ 80421421917316 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j<188 := by omega
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic root_at_1855 hpre with ⟨rfl,rfl⟩
  have hcomp := rootIter_complete htail
  intro hA
  subst A
  have hmem : some 80421421917316 ∈ secondWindowFirsts := by
    unfold secondWindowFirsts
    apply List.mem_map.mpr
    refine ⟨j,List.mem_range.mpr hj,?_⟩
    rw [hcomp]
    rfl
  exact second_target_not_in_window hmem

/-- The only possible MiddleOdd predecessor first counter for the k=1
    dangerous anchor is 80,421,421,917,316.  It never occurs on the authentic
    root orbit with the MiddleOdd guard. -/
theorem second_mixed_anchor_middleOdd_predecessor_unreachable
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hR : 4*a+6=321685687669270)
    (h1 : a<d)
    (h2 : d<3*a+1) :
    False := by
  have ha : a=80421421917316 := by omega
  subst a
  by_cases hEarly : n≤1854
  · have hs := root_sum_before_1855 hEarly hr
    omega
  by_cases hLate : 2043≤n
  · have hs := root_sum_after_2042 hLate hr
    omega
  exact (second_window_first_not_target (by omega) (by omega) hr) rfl

theorem dangerR_one :
    dangerR 1 = 321685687669270 := by
  decide

/-- The k=1 source-faithful H^46/F terminal anchor is also absent from the
    authentic root small-anchor orbit. -/
theorem second_danger_anchor_not_root
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR 1) 1) :
    False := by
  have hm := danger_anchor_requires_middleOdd hr ha
  rw [dangerR_one] at hm
  exact second_mixed_anchor_middleOdd_predecessor_unreachable
    hr hm.2.2.2 hm.1 hm.2.1

#print axioms root_at_1854
#print axioms root_at_1855
#print axioms root_at_2043
#print axioms second_target_not_in_window
#print axioms second_mixed_anchor_middleOdd_predecessor_unreachable
#print axioms second_danger_anchor_not_root
end BB6.Agent31F321SecondMixed
