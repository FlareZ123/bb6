import GateNecessary
import ManyShield

namespace CascadeRootMinIndex
open CascadeSource CascadeSweep CascadeManyShield CascadeSmallFatal CascadeNecessaryGate

theorem orbit_trans {s t u : Nat × Nat}
    (h : Orbit s t) (k : Orbit t u) : Orbit s u := by
  induction h with
  | refl => exact k
  | step he hr ih => exact Orbit.step he (ih k)

theorem reach_to_orbit {s t : Nat × Nat}
    (h : ReachC s t) : Orbit s t := by
  induction h with
  | refl => exact Orbit.refl _
  | push hp he ih => exact orbit_trans ih (Orbit.step he (Orbit.refl _))

/-- Every fatal reset through n=100 is globally absent from the rooted orbit. -/
theorem no_fatal_through_100 (n : Nat) (hn : n ≤ 100) :
    ¬ReachC (2,0) (4*2^n-n-4,0) := by
  by_cases hs : n < 6
  · exact no_small_index n hs
  by_cases hc : n%6=0∨n%6=1∨n%6=2∨n%6=3
  · exact all_four_class_indices n hc
  have ht : n%6=4∨n%6=5 := by omega
  intro hr
  have ho := reach_to_orbit hr
  exact blank_excludes_surviving_fatal_through_100 n (by omega) hn ht ho

/-- Any compressed source-orbit halt requires a candidate fatal index ≥101. -/
theorem halt_requires_index_ge_101 (a : Nat) (h : ReachC (2,0) (a,1)) :
    ∃ n, 101 ≤ n ∧ (n%6=4∨n%6=5) ∧
      ReachC (2,0) (4*2^n-n-4,0) := by
  obtain ⟨n,hn,hres,hr⟩ := halt_requires_surviving_gate a h
  have hbig : 101 ≤ n := by
    by_cases hb : n ≤ 100
    · exact False.elim (no_fatal_through_100 n hb hr)
    · omega
  exact ⟨n,hbig,hres,hr⟩

#print axioms reach_to_orbit
#print axioms no_fatal_through_100
#print axioms halt_requires_index_ge_101
end CascadeRootMinIndex
