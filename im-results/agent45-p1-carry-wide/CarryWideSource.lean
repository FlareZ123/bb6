import P1CarryBlankArithmetic
import P1Gate
import CarryWideArithmetic

namespace BB6.Agent45CarryWide
open BB6.P1CarryExact BB6.P1CarryExtinction BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction

theorem wide_left (n K b d m : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m) :
    16≤b ∧ 6*2^(n-m)<(b+12)/2 := by
  have hm := critical_cost_lt n K b d m hn hK hKn hz h
  have hM := source_to_micro n b d m hn h
  have hlow := (micro_scaled_lower n m ((d-1)/2) ((b+12)/2)
    hn hM (by omega)).2
  have hbounds := (micro_bounds n m ((d-1)/2) ((b+12)/2)
    hn hM (by omega)).2.2 (by omega)
  have hbig := pow2_ge_1100_mul n hn
  have hpos : 6*2^n < total n-n-2 := by simp [total]; omega
  exact ⟨by omega, scaled_left_strict n m _ (by omega) (by omega)⟩

theorem wide_inverse_cost (n K b d m t k c : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c)) : m+t<K := by
  have hlarge := (wide_left n K b d m hK hn hKn hz h).1
  cases t with
  | zero => simpa using critical_cost_lt n K b d m hn hK hKn hz h
  | succ t =>
    obtain ⟨k0,c0,hi0,hc0⟩ := inverse_prev_odd b d t k c hi
    have hk := inverse_k_lower b d t k0 c0 hi0
    have hc := OddCone.parent b d m t k0 c0 h (by omega) hb4 hd hi0 (by omega) hc0
    have hcost := critical_cost_lt n K _ _ _ hn hK hKn hz hc
    omega

theorem wide_no_one (n K b d m k : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) : ¬ GAncestor b d k 1 := by
  intro ha
  obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
  have hlarge := (wide_left n K b d m hK hn hKn hz h).1
  have hk := ancestor_k_lower b d k 1 ha
  have hc := OddCone.parent b d m t k 1 h (by omega) hb4 hd hi (by omega) (by decide)
  exact source_width_zero_no_right_five n K _ _ (by omega) hK (by omega) hz hc

theorem wide_even_gap (n K b d m t k c : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 7*2^n<2*k+8 ∧ 2*k+8<14*2^n := by
  have hlarge := (wide_left n K b d m hK hn hKn hz h).1
  have hcost := wide_inverse_cost n K b d m t k c hK hn hKn hmargin hz h hb4 hd hi
  have hmass := odd_cone_mass _ _ b d m h
  have hroot : criticalLeft n+3+2*n+13=14*2^n := by
    unfold criticalLeft
    have hp := pow2_ge_1100_mul n (by omega)
    omega
  have hMass : b+d+2*m+2*n+13=14*2^n := by omega
  have hback := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hpower := inverseAt_power b d t k c hi
  exact even_gap n K b d m t k c hKn hcost hmargin hb4 hd hc
    (wide_left n K b d m hK hn hKn hz h).2 hMass hback hpower
    (pow2_ge_1100_mul n hn)

theorem wide_even_no_power (n K b d m t k c j : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (hz : width K n=0)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb4 : b%4=0) (hd : d%2=1) (hi : inverseAt b d t=some (k,c))
    (hc : c%2=0) : 2*k+8≠14*2^j := by
  obtain ⟨hl,hr⟩ := wide_even_gap n K b d m t k c hK hn hKn hmargin hz h hb4 hd hi hc
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

theorem wide_cone_no_reach (n K r : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (hz : width K n=0) :
    ∀ b d m, K-m=r → OddCone (criticalLeft n) 3 b d m → ¬ BB6.Agent1.Reach b d := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro b d m hr h hReach
    have hcost := critical_cost_lt n K b d m hn hK hKn hz h
    have hlarge := (wide_left n K b d m hK hn hKn hz h).1
    have hrootEven : criticalLeft n%2=0 := by
      unfold criticalLeft
      have hp := pow2_ge_1100_mul n (by omega)
      omega
    have hbe := source_even_left _ _ _ _ _ hrootEven h
    have hdo := source_odd_right _ _ _ _ _ (by decide) h
    have hpar := BB6.Agent1.reachable_even_mod4 b d hReach (by omega) hbe
    have hb4 : b%4=0 := by rcases hpar with h2 | h4 <;> omega
    have hno : ∀ k, ¬ GAncestor b d k 1 := fun k =>
      wide_no_one n K b d m k hK hn hKn hmargin hz h hb4 hdo
    obtain ⟨k,c,ha,hc,hpre⟩ := BB6.Agent50P1.positive_G_feeder b d
      (by omega) hb4 (by omega) hno hReach
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
    have hk := inverse_k_lower b d t k c hi
    by_cases heven : c%2=0
    · obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (2*k-4) (c+4)
        hpre (by omega) (by omega) (by omega)
      exact wide_even_no_power n K b d m t k c j hK hn hKn hmargin hz h hb4 hdo hi heven (by omega)
    · have hchild := OddCone.parent b d m t k c h (by omega) hb4 hdo hi (by omega) (by omega)
      have hnew := critical_cost_lt n K _ _ _ hn hK hKn hz hchild
      exact ih (K-(m+t+1)) (by omega) _ _ _ rfl hchild hpre

/-- Every original critical hub with a sufficiently early empty carry layer
    is excluded from the authentic blank-entry Reach relation. -/
theorem wide_hub_no_reach_of_empty (n K : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (hz : width K n=0) : ¬ BB6.Agent1.Reach (criticalLeft n) 3 :=
  wide_cone_no_reach n K K hK hn hKn hmargin hz _ _ 0 (by omega) OddCone.root

/-- Critical positive reset counter, even or odd index. Odd n is ruled out
    by the original positive-even reset power invariant. -/
theorem wide_reset_no_reach_of_empty (n K : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (hz : width K n=0) :
    ¬ BB6.Agent1.Reach 2 (14*2^n-2*n-10) := by
  intro h
  have hp := pow2_ge_1100_mul n (by omega)
  have he : (2:Nat)^n%2=0 := by
    apply Nat.dvd_iff_mod_eq_zero.mp
    have hd := Nat.pow_dvd_pow 2 (show 1≤n by omega)
    simpa using hd
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  by_cases hnEven : n%2=0
  · have hmod : d%4=2 := by dsimp [d]; omega
    have hreach := BB6.Agent50P1.critical_target_implies_three d hd hmod h
    have heq : d-6=criticalLeft n := by dsimp [d,criticalLeft]; omega
    rw [heq] at hreach
    exact wide_hub_no_reach_of_empty n K hK hn hKn hmargin hz hreach
  · have hmod : d%4=0 := by dsimp [d]; omega
    obtain ⟨j,hj⟩ := BB6.Agent1.reset_four_power d h (by omega) hmod
    have hl : 7*2^n<d+8 := by dsimp [d]; omega
    have hr : d+8<14*2^n := by dsimp [d]; omega
    by_cases hjn : n≤j
    · have hpow := Nat.pow_le_pow_right (show 0<2 by decide) hjn
      omega
    · have hpow := Nat.pow_le_pow_right (show 0<2 by decide) (show j≤n-1 by omega)
      have hsplit : 2^n=2*2^(n-1) := by
        have hidx : n=n-1+1 := by omega
        calc
          2^n = 2^(n-1+1) := congrArg (fun i : Nat => 2^i) hidx
          _ = 2*2^(n-1) := by rw [Nat.pow_succ]; ac_rfl
      omega

theorem wide_reset_requires_width (n K : Nat) (hK : 0<K)
    (hn : 14≤n) (hKn : K≤n) (hmargin : n+K < 12*2^(n-K)) (h : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) : 0<width K n := by
  by_cases hz : width K n=0
  · exact False.elim (wide_reset_no_reach_of_empty n K hK hn hKn hmargin hz h)
  · omega

#print axioms wide_cone_no_reach
#print axioms wide_reset_no_reach_of_empty
#print axioms wide_reset_requires_width
end BB6.Agent45CarryWide
