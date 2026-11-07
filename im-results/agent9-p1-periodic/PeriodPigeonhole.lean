import Std
namespace PeriodPigeonhole

/-- A cycle with S distinct positive integer residues below S cannot exist.
    This is the finite-state part of the binary marker shortening argument. -/
theorem no_primitive_full_cycle (S : Nat) (hS : 0<S) (f : Nat → Nat)
    (hbound : ∀ i<S, 0<f i ∧ f i<S)
    (hinj : ∀ i<S, ∀ j<S, f i=f j → i=j) : False := by
  let xs := (List.range S).map (fun i => f i-1)
  have hx : xs.Nodup := by
    apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map]
    apply List.Pairwise.imp_of_mem (l:=List.range S)
      (R:=fun i j => i ≠ j) (S:=fun i j => f i-1 ≠ f j-1)
    · intro i j hi hj hn he
      have hp := hbound i (List.mem_range.mp hi)
      have hq := hbound j (List.mem_range.mp hj)
      have heq : f i=f j := by omega
      exact hn (hinj i (List.mem_range.mp hi) j (List.mem_range.mp hj) heq)
    · exact List.nodup_iff_pairwise_ne.mp List.nodup_range
  have hsub : xs ⊆ List.range (S-1) := by
    intro x hxmem
    obtain ⟨i,hi, rfl⟩ := List.mem_map.mp hxmem
    apply List.mem_range.mpr
    have hp := hbound i (List.mem_range.mp hi)
    omega
  have hc := List.Nodup.length_le_of_subset hx hsub
  simp only [xs,List.length_map,List.length_range] at hc
  omega

#print axioms no_primitive_full_cycle
end PeriodPigeonhole
