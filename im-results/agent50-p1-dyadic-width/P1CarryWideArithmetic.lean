import P1CarryWideMargin
namespace BB6.P1CarryExact
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction BB6.P1CarryExtinction

/-- The predecessor at depth t-1 gives a genuine odd cone child of cost
    m+t. Thus the depth of ANY inverseAt output is controlled by extinction. -/
theorem critical_inverse_cost_full (n K b d m t k c : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c)) : m+t<K := by
  have hlarge := critical_large_left_full n K b d m hK hn hKn hz h
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
theorem critical_no_one_full (n K b d m k : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) : ¬ GAncestor b d k 1 := by
  intro ha
  obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
  have hlarge := critical_large_left_full n K b d m hK hn hKn hz h
  have hk := ancestor_k_lower b d k 1 ha
  have hc := OddCone.parent b d m t k 1 h (by omega) hb4 hd hi (by omega) (by decide)
  exact source_width_zero_no_right_five n K _ _ (by omega) hK (by omega) hz hc

/-- The lower left bound separates every even output from the two adjacent
    powers of 14. No restriction to a particular feeder sector is used. -/
theorem critical_even_gap_full (n K b d m t k c : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 7*2^n<2*k+8 ∧ 2*k+8<14*2^n := by
  have hlarge := critical_large_left_full n K b d m hK hn hKn hz h
  have hcost := critical_inverse_cost_full n K b d m t k c hK hn hKn hz h hb4 hd hi
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

theorem critical_even_no_power_full (n K b d m t k c j : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 2*k+8≠14*2^j := by
  obtain ⟨hl,hr⟩ := critical_even_gap_full n K b d m t k c hK hn hKn hz h hb4 hd hi hc
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

#print axioms critical_inverse_cost_full
#print axioms critical_no_one_full
#print axioms critical_even_no_power_full
end BB6.P1CarryExact
