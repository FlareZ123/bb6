import RootMinIndex
import FastShield

namespace CascadeRootMin256
open CascadeSource CascadeSweep CascadeManyShield CascadeSmallFatal
open CascadeRootMinIndex

/-- Exact rooted accelerated C-orbit never hits any indexed fatal reset
    with exponent at most 256, in any residue class. -/
theorem no_fatal_through_256 (n : Nat) (hn : n≤256) :
    ¬ReachC (2,0) (fatal n,0) := by
  by_cases hs : n<6
  · exact no_small_index n hs
  by_cases hc : n%6=0∨n%6=1∨n%6=2∨n%6=3
  · exact all_four_class_indices n hc
  have hres : n%6=4∨n%6=5 := by omega
  intro hr
  exact CascadeFastShield.blank_excludes_surviving_through_256 n
    (by omega) hn hres (reach_to_orbit hr)

/-- A halt of the rooted compressed C system has a remaining fatal
    exponent n>=257 in residue class 4 or 5 mod 6. -/
theorem halt_requires_index_ge_257 (a : Nat)
    (h : ReachC (2,0) (a,1)) :
    ∃ n, 257≤n ∧ (n%6=4∨n%6=5) ∧
      ReachC (2,0) (fatal n,0) := by
  obtain ⟨n,_,hmod,hr⟩ := halt_requires_index_ge_101 a h
  have hn : 257≤n := by
    by_contra hb
    have hs : n≤256 := by omega
    exact no_fatal_through_256 n hs hr
  exact ⟨n,hn,hmod,hr⟩

#print axioms no_fatal_through_256
#print axioms halt_requires_index_ge_257
end CascadeRootMin256
