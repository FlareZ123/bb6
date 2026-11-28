import FirstMixedAnchorExclusion
import Lean.Elab.Tactic.Omega

/-!
Reusable all-time root exclusion criterion for MiddleOdd predecessor targets.

A target first counter is excluded globally once:
1. an exact root checkpoint immediately before a finite window has sum below
   the target's entire MiddleOdd sum band;
2. an exact checkpoint after the window has sum above that band; and
3. exact executable/source equivalence proves the target first counter absent
   inside the window.

Strict source-sum growth turns these three local certificates into an
all-time theorem.
-/

namespace BB6.Agent31F321DangerWindow
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed

theorem root_first_absent_in_exact_window
    {startN width startA startD target n A D : Nat}
    (hstart : CounterReach 1 1 startN startA startD)
    (hlo : startN ≤ n)
    (hhi : n < startN + width)
    (habs :
      some target ∉
        (List.range width).map fun j =>
          (rootIter j startA startD).map Prod.fst)
    (hr : CounterReach 1 1 n A D) :
    A ≠ target := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hlo
  have hj : j < width := by omega
  rcases counterReach_split hr with ⟨a,d,hpre,htail⟩
  rcases counterReach_deterministic hstart hpre with ⟨rfl,rfl⟩
  have hcomp := rootIter_complete htail
  intro hA
  subst A
  apply habs
  apply List.mem_map.mpr
  refine ⟨j,List.mem_range.mpr hj,?_⟩
  rw [hcomp]
  rfl

/-- Generic all-time exclusion of a MiddleOdd predecessor first counter.

For a MiddleOdd predecessor with first counter target, its sum lies in the
closed interval [2*target+1, 4*target]. A checkpoint below that interval,
a checkpoint above it, strict sum growth, and exact absence in the intervening
finite window exclude the target at every root time.
-/
theorem middleOdd_target_unreachable_of_window
    {preN startN width endN
      preA preD startA startD endA endD target n d : Nat}
    (hstartN : startN = preN + 1)
    (hendN : endN = startN + width)
    (hpre : CounterReach 1 1 preN preA preD)
    (hstart : CounterReach 1 1 startN startA startD)
    (hend : CounterReach 1 1 endN endA endD)
    (hpreSum : preA + preD < 2*target + 1)
    (hendSum : 4*target < endA + endD)
    (habs :
      some target ∉
        (List.range width).map fun j =>
          (rootIter j startA startD).map Prod.fst)
    (hr : CounterReach 1 1 n target d)
    (h1 : target < d)
    (h2 : d < 3*target + 1) :
    False := by
  have htargetLow : 2*target+1 ≤ target+d := by omega
  have htargetHigh : target+d ≤ 4*target := by omega
  by_cases hEarly : n ≤ preN
  · obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le hEarly
    have hpre' : CounterReach 1 1 (n+m) preA preD := by
      simpa [←hm] using hpre
    rcases counterReach_split hpre' with ⟨a0,d0,hprefix,htail⟩
    rcases counterReach_deterministic hr hprefix with ⟨rfl,rfl⟩
    have hs := counterReach_sum_mono htail
    omega
  by_cases hLate : endN ≤ n
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hLate
    rcases counterReach_split hr with ⟨a0,d0,hprefix,htail⟩
    rcases counterReach_deterministic hend hprefix with ⟨rfl,rfl⟩
    have hs := counterReach_sum_mono htail
    omega
  have hlo : startN ≤ n := by omega
  have hhi : n < startN + width := by omega
  have hne := root_first_absent_in_exact_window
    hstart hlo hhi habs hr
  exact hne rfl

#print axioms root_first_absent_in_exact_window
#print axioms middleOdd_target_unreachable_of_window
end BB6.Agent31F321DangerWindow
