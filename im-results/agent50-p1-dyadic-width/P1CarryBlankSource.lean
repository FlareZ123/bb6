import P1CarryBlankArithmetic
import P1Gate

/-! Original blank-reachability exclusion for every critical index with
    one empty early carry layer. No artificial inverse cost cap. -/
namespace BB6.P1CarryExact
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction BB6.P1CarryExtinction

/-- All original odd-cone states with the critical root are unreachable
    once an early layer is empty. Induction is on the remaining cost. -/
theorem critical_cone_no_reach (n K r : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0) :
    ∀ b d m, K-m=r → OddCone (criticalLeft n) 3 b d m → ¬ BB6.Agent1.Reach b d := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro b d m hr h hReach
    have hcost := critical_cost_lt n K b d m (by omega) hK (by omega) hz h
    have hlarge := critical_large_left n K b d m hK hn hz h
    have hrootEven : criticalLeft n%2=0 := by
      unfold criticalLeft
      have hp := pow2_ge_1100_mul n (by omega)
      omega
    have hbe := source_even_left _ _ _ _ _ hrootEven h
    have hdo := source_odd_right _ _ _ _ _ (by decide) h
    have hpar := BB6.Agent1.reachable_even_mod4 b d hReach (by omega) hbe
    have hb4 : b%4=0 := by rcases hpar with h2 | h4 <;> omega
    have hno : ∀ k, ¬ GAncestor b d k 1 := fun k =>
      critical_no_one n K b d m k hK hn hz h hb4 hdo
    obtain ⟨k,c,ha,hc,hpre⟩ := BB6.Agent50P1.positive_G_feeder b d
      (by omega) hb4 (by omega) hno hReach
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
    have hk := inverse_k_lower b d t k c hi
    by_cases heven : c%2=0
    · obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (2*k-4) (c+4)
        hpre (by omega) (by omega) (by omega)
      exact critical_even_no_power n K b d m t k c j hK hn hz h hb4 hdo hi heven (by omega)
    · have hchild := OddCone.parent b d m t k c h (by omega) hb4 hdo hi (by omega) (by omega)
      have hnew := critical_cost_lt n K _ _ _ (by omega) hK (by omega) hz hchild
      exact ih (K-(m+t+1)) (by omega) _ _ _ rfl hchild hpre

/-- Every original critical hub with a sufficiently early empty carry layer
    is excluded from the authentic blank-entry Reach relation. -/
theorem critical_hub_no_reach_of_empty (n K : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0) : ¬ BB6.Agent1.Reach (criticalLeft n) 3 :=
  critical_cone_no_reach n K K hK hn hz _ _ 0 (by omega) OddCone.root

/-- Critical positive reset counter, even or odd index. Odd n is ruled out
    by the original positive-even reset power invariant. -/
theorem critical_reset_no_reach_of_empty (n K : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (hz : width K n=0) :
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
    exact critical_hub_no_reach_of_empty n K hK hn hz hreach
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

theorem critical_reset_requires_width (n K : Nat) (hK : 0<K)
    (hn : 2*K+28≤n) (h : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) : 0<width K n := by
  by_cases hz : width K n=0
  · exact False.elim (critical_reset_no_reach_of_empty n K hK hn hz h)
  · omega

#print axioms critical_cone_no_reach
#print axioms critical_hub_no_reach_of_empty
#print axioms critical_reset_no_reach_of_empty
#print axioms critical_reset_requires_width
end BB6.P1CarryExact
