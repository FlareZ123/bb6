import P1CriticalValuation
import P1InverseLog

namespace BB6.Agent47P1
open BB6.P1Reduction

/-- The exact root inverse list for critical index n. It uses only
floor(log2(n+2))+1 checks, whereas the hub coordinates grow as 2^n. -/
def criticalRootList (n : Nat) : List (Nat × Nat) :=
  ((List.range (Nat.log2 (n+2)+1)).filterMap
    (inverseAt (14*2^n-2*n-16) 3))

/-- The logarithmic-in-n bounded list contains EVERY first-level
G inverse of the P1 halting-critical hub, for all n>=4. -/
theorem critical_ancestor_iff_mem (n k c : Nat) (hn : 4 ≤ n) :
    GAncestor (14*2^n-2*n-16) 3 k c ↔
    (k,c) ∈ criticalRootList n := by
  constructor
  · intro h
    obtain ⟨t,ht,_⟩ := inverseAt_complete _ _ k c h
    have hs :
        3+(14*2^n-2*n-16)/2+3 = 2^t*(c+3) :=
      inverseAt_power _ _ t k c ht
    have hd : 2^t ∣ n+2 :=
      (critical_hub_shift_all_powers n t hn).mp ⟨c+3,hs⟩
    have hle : t ≤ Nat.log2 (n+2) :=
      (Nat.le_log2 (by omega : n+2 ≠ 0)).mpr
        (Nat.le_of_dvd (by omega) hd)
    simp only [criticalRootList, List.mem_filterMap]
    exact ⟨t,by simpa using Nat.lt_succ_of_le hle,ht⟩
  · intro h
    simp only [criticalRootList, List.mem_filterMap] at h
    obtain ⟨t,_,ht⟩ := h
    exact inverseAt_sound _ _ t k c ht

#print axioms critical_ancestor_iff_mem
end BB6.Agent47P1
