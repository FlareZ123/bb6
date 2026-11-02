import P1FiniteInverse

namespace BB6.Agent47P1
open BB6.P1Reduction

/-- The executable inverse enumeration index is exactly the binary power
exponent in the source GAncestor relation. -/
theorem inverseAt_power (b d t k c : Nat)
    (h : inverseAt b d t = some (k,c)) :
    d + b/2 + 3 = 2^t*(c+3) := by
  induction t generalizing k c with
  | zero =>
      simp only [inverseAt] at h
      split at h
      · next hcond =>
        obtain ⟨hb,hmod⟩ := hcond
        have hk : b = 4*(b/4-1)+4 := by omega
        have hc : d+b/2 = d+2*(b/4-1)+2 := by omega
        obtain ⟨hk',hc'⟩ := Prod.mk.inj (Option.some.inj h)
        simp [hc', Nat.pow_zero]
      · simp at h
  | succ t ih =>
      simp only [inverseAt] at h
      split at h
      · simp at h
      · next k0 c0 heq =>
        split at h
        · next hcond =>
          obtain ⟨hc3,hodd⟩ := hcond
          have hp := ih k0 c0 heq
          obtain ⟨hk',hc'⟩ := Prod.mk.inj (Option.some.inj h)
          have hcv : c0 = 2*c+3 := by omega
          calc
            d+b/2+3 = 2^t*(c0+3) := hp
            _ = 2^(t+1)*(c+3) := by
              rw [hcv, Nat.pow_succ]
              have hlin : (2*c+3)+3=2*(c+3) := by omega
              rw [hlin, Nat.mul_assoc]
        · cases h

/-- Every computed inverse depth is logarithmic in the initial shifted
right counter. The bound applies to arbitrary positive G output values. -/
theorem inverseAt_log_bound (b d t k c : Nat)
    (h : inverseAt b d t = some (k,c)) :
    t ≤ Nat.log2 (d+b/2+3) := by
  have hp := inverseAt_power b d t k c h
  have hle : 2^t ≤ d+b/2+3 := by
    rw [hp]
    have hpos : 0 < c+3 := by omega
    exact Nat.le_mul_of_pos_right (2^t) hpos
  exact (Nat.le_log2 (by omega : d+b/2+3 ≠ 0)).mpr hle

/-- Efficient inversion with a number of iterations at most logarithmic
in the potentially astronomical output counter. -/
def inverseListLog (b d : Nat) : List (Nat × Nat) :=
  ((List.range (Nat.log2 (d+b/2+3)+1)).filterMap (inverseAt b d))

theorem inverse_iff_mem_log (b d k c : Nat) :
    GAncestor b d k c ↔ (k,c) ∈ inverseListLog b d := by
  constructor
  · intro h
    obtain ⟨t,ht,_⟩ := inverseAt_complete b d k c h
    have hb := inverseAt_log_bound b d t k c ht
    simp only [inverseListLog, List.mem_filterMap]
    exact ⟨t, by simpa using Nat.lt_succ_of_le hb, ht⟩
  · intro h
    simp only [inverseListLog, List.mem_filterMap] at h
    obtain ⟨t,_,ht⟩ := h
    exact inverseAt_sound b d t k c ht

#print axioms inverseAt_power
#print axioms inverseAt_log_bound
#print axioms inverse_iff_mem_log
end BB6.Agent47P1
