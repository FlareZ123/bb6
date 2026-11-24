import P1CarryExactReverse

/-! A single empty carry layer excludes every possible exceptional odd input
    and every positive even-right terminal feeder of the critical root. -/
namespace BB6.P1CarryExact
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction BB6.P1CarryExtinction

def criticalLeft (n : Nat) : Nat := 14*2^n-2*n-16

theorem critical_cost_lt (n K b d m : Nat) (hn : 14≤n) (hK : 0<K)
    (hKn : K≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m) : m<K := by
  by_cases hm : K≤m
  · have hw := (source_width_iff n K hn hK hKn).mpr ⟨b,d,m,hm,h⟩
    omega
  · omega

/-- Even for unrestricted depths, an extinct prefix forces every source
    left counter far above the small exceptional reset at b=2. -/
theorem critical_large_left (n K b d m : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m) : n+3*K+10≤b/4 := by
  have hm := critical_cost_lt n K b d m (by omega) hK (by omega) hz h
  have hM := source_to_micro n b d m (by omega) h
  have hlow := (micro_scaled_lower n m ((d-1)/2) ((b+12)/2)
    (by omega) hM (by omega)).2
  have hbig := pow2_ge_1100_mul n (by omega)
  have hpos : 6*2^n < total n-n-2 := by simp [total]; omega
  have he : 2^m * 2^(n-m)=2^n := by rw [← Nat.pow_add]; congr 1; omega
  have hw : 6*2^(n-m)≤(b+12)/2 := by
    by_cases hw0 : 6*2^(n-m)≤(b+12)/2
    · exact hw0
    · have hp := Nat.mul_le_mul_left (2^m) (show (b+12)/2≤6*2^(n-m) by omega)
      have hx : 2^m*(6*2^(n-m))=6*2^n := by
        rw [← he]; ac_rfl
      omega
  have hpow := pow2_ge_1100_mul (n-m) (by omega)
  omega

theorem ancestor_k_lower (b d k c : Nat) (h : GAncestor b d k c) : b/4-1≤k := by
  induction h with
  | upper k d => omega
  | nest b d k c h ih => omega

theorem inverse_k_lower (b d t k c : Nat) (h : inverseAt b d t=some (k,c)) : b/4-1≤k :=
  ancestor_k_lower b d k c (inverseAt_sound b d t k c h)

/-- Every nonzero inverse depth is preceded by an actual odd output. -/
theorem inverse_prev_odd (b d t k c : Nat)
    (h : inverseAt b d (t+1)=some (k,c)) :
    ∃ k0 c0, inverseAt b d t=some (k0,c0) ∧ c0%2=1 := by
  simp only [inverseAt] at h
  split at h
  · simp at h
  · next k0 c0 heq =>
    split at h
    · next hcond => exact ⟨k0,c0,heq,hcond.2⟩
    · simp at h

/-- The predecessor at depth t-1 gives a genuine odd cone child of cost
    m+t. Thus the depth of ANY inverseAt output is controlled by extinction. -/
theorem critical_inverse_cost (n K b d m t k c : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c)) : m+t<K := by
  have hlarge := critical_large_left n K b d m hK hn hz h
  cases t with
  | zero => simpa using critical_cost_lt n K b d m (by omega) hK (by omega) hz h
  | succ t =>
    obtain ⟨k0,c0,hi0,hc0⟩ := inverse_prev_odd b d t k c hi
    have hk := inverse_k_lower b d t k0 c0 hi0
    have hc := OddCone.parent b d m t k0 c0 h (by omega) hb4 hd hi0 (by omega) hc0
    have hcost := critical_cost_lt n K _ _ _ (by omega) hK (by omega) hz hc
    omega

/-- The exceptional G-input c=1 is absent at every genuine critical-cone
    node when any sufficiently early carry layer is empty. -/
theorem critical_no_one (n K b d m k : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) : ¬ GAncestor b d k 1 := by
  intro ha
  obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
  have hlarge := critical_large_left n K b d m hK hn hz h
  have hk := ancestor_k_lower b d k 1 ha
  have hc := OddCone.parent b d m t k 1 h (by omega) hb4 hd hi (by omega) (by decide)
  exact source_width_zero_no_right_five n K _ _ (by omega) hK (by omega) hz hc

/-- The lower left bound separates every even output from the two adjacent
    powers of 14. No restriction to a particular feeder sector is used. -/
theorem critical_even_gap (n K b d m t k c : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 7*2^n<2*k+8 ∧ 2*k+8<14*2^n := by
  have hlarge := critical_large_left n K b d m hK hn hz h
  have hcost := critical_inverse_cost n K b d m t k c hK hn hz h hb4 hd hi
  have hmass := odd_cone_mass _ _ b d m h
  have hroot : criticalLeft n+3+2*n+13=14*2^n := by
    unfold criticalLeft
    have hp := pow2_ge_1100_mul n (by omega)
    omega
  have hMass : b+d+2*m+2*n+13=14*2^n := by omega
  have hback := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hpower := inverseAt_power b d t k c hi
  have ht : 1≤t := by
    by_cases hzero : t=0
    · subst t; simp at hpower; omega
    · omega
  have hpow : 2≤2^t := by
    have hp := Nat.pow_le_pow_right (show 0<2 by decide) ht
    simpa using hp
  have hcBound : 2*(c+3)≤d+b/2+3 := by
    rw [hpower]
    exact Nat.mul_le_mul_right (c+3) hpow
  omega

theorem critical_even_no_power (n K b d m t k c j : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 2*k+8≠14*2^j := by
  obtain ⟨hl,hr⟩ := critical_even_gap n K b d m t k c hK hn hz h hb4 hd hi hc
  intro he
  by_cases hj : n≤j
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) hj
    omega
  · have hp := Nat.pow_le_pow_right (show 0<2 by decide) (show j≤n-1 by omega)
    have hsplit : 2^n=2*2^(n-1) := by
      have heq : n=n-1+1 := by omega
      calc
        2^n = 2^(n-1+1) := congrArg (fun i : Nat => 2^i) heq
        _ = 2*2^(n-1) := by rw [Nat.pow_succ]; ac_rfl
    omega

#print axioms critical_large_left
#print axioms critical_inverse_cost
#print axioms critical_no_one
#print axioms critical_even_no_power
end BB6.P1CarryExact
