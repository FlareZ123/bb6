import SmallFatal

namespace CascadeNecessaryGate
open CascadeSource CascadeSweep CascadeAncestry CascadeSmallFatal

/-- A reached halting C-state is always descended from an earlier indexed
    fatal reset, with the index equal to the sweep exponent remembered by
    the source-aligned phase invariant. -/
theorem halt_has_indexed_reset (a : Nat)
    (h : ReachC (2,0) (a,1)) :
    ∃ n, ReachC (2,0) (4*2^n-n-4,0) := by
  have ht := CascadeAncestry.tagged_reachable h
  change CascadeAncestry.Tagged a 1 at ht
  rcases ht with hb|hb|⟨hh,n,hhr,ha,hform,hodd⟩
  · omega
  · omega
  · have hp : 1≤2^n := Nat.one_le_pow n 2 (by omega)
    have hform' : hh+n+4=4*2^n := by omega
    have hlarge : n+4≤4*2^n := by omega
    have hval : hh=4*2^n-n-4 := by omega
    exact ⟨n,by rw [←hval]; exact hhr⟩

/-- A halt of machine #746's exact copied C dynamics requires a blank-reached
    fatal reset with n>=6 and n mod 6 in the two complementary classes.
    All four other classes and the six small indices are ruled out uniformly. -/
theorem halt_requires_surviving_gate (a : Nat)
    (h : ReachC (2,0) (a,1)) :
    ∃ n, 6≤n ∧ (n%6=4∨n%6=5) ∧
      ReachC (2,0) (4*2^n-n-4,0) := by
  obtain ⟨n,hr⟩ := halt_has_indexed_reset a h
  have hn : 6≤n := by
    by_cases hs : n<6
    · exact False.elim (CascadeSmallFatal.no_small_index n hs hr)
    · omega
  by_cases hc : n%6=0∨n%6=1∨n%6=2∨n%6=3
  · exact False.elim (CascadeSmallFatal.all_four_class_indices n hc hr)
  · have hother : n%6=4∨n%6=5 := by omega
    exact ⟨n,hn,hother,hr⟩

#print axioms halt_has_indexed_reset
#print axioms halt_requires_surviving_gate
end CascadeNecessaryGate
