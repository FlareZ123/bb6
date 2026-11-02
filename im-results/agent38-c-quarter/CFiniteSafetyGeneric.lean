import CFiniteSafety

namespace BB6Agent38

/-- A reusable Machine C halting-gateway exclusion protocol. A verified
    live endpoint, a gateway-free suffix, rank monotonicity, and a bound
    on the delay from gateway entry to stopping imply all-time exclusions. -/
theorem gateway_exclusion_from_safe_tail
    (N T D B : Nat) (tailState endState : S)
    (hlen : N = T+D)
    (hprefix : run T (some (5,0,1)) = some tailState)
    (hend : run N (some (5,0,1)) = some endState)
    (hsafe : ∀ i, i ≤ D → ∀ t, run i (some tailState) = some t → ¬thinS t)
    (hdelay : ∀ j, j ≤ B → 4*j+5 ≤ D)
    (hrank : ∀ j, j ≤ B → rank (0,2*j,4*j+10) < rank endState)
    (j : Nat) (hj : j ≤ B) :
    ¬ ∃ n, run n (some (5,0,1)) = some (0,2*j,4*j+10) := by
  rintro ⟨n,hn⟩
  by_cases hbefore : n ≤ T
  · have htime : n+(4*j+5) ≤ N := by
      have hd := hdelay j hj
      omega
    have hhalt : run (n+(4*j+5)) (some (5,0,1)) = none := by
      rw [show n+(4*j+5) = (4*j+5)+n by omega,run_add,hn,thin_halts]
    have hN : N=(N-(n+(4*j+5)))+(n+(4*j+5)) := by omega
    have hbad : run N (some (5,0,1)) = none := by
      rw [hN,run_add,hhalt,run_none]
    rw [hend] at hbad
    contradiction
  · by_cases hmid : n ≤ N
    · have hafter : n=(n-T)+T := by omega
      have hlength : n-T ≤ D := by omega
      have hs : run (n-T) (some tailState) = some (0,2*j,4*j+10) := by
        rw [hafter,run_add,hprefix] at hn
        exact hn
      have hno := hsafe (n-T) hlength (0,2*j,4*j+10) hs
      have hyes : thinS (0,2*j,4*j+10) := by simp [thinS] <;> omega
      exact hno hyes
    · have hafter : n=(n-N)+N := by omega
      have hs : run (n-N) (some endState) = some (0,2*j,4*j+10) := by
        rw [hafter,run_add,hend] at hn
        exact hn
      have hm := rank_run_nondecreasing (n-N) endState (0,2*j,4*j+10) hs
      have hg := hrank j hj
      omega

/-- Optimal *numerical* gateway index certified by a fixed successful endpoint
    and a fixed safe suffix. The two constraints are the forced halting
    countdown 4j+5 and strict rank comparison 8j+10<R(end). -/
def maxSafeIndex (D : Nat) (endState : S) : Nat :=
  min ((D-5)/4) ((rank endState-11)/8)

/-- For a live prefix and gateway-free suffix, all thin gateway indices
    at most maxSafeIndex are excluded at every future time. -/
theorem gateway_exclusion_optimal_bound
    (N T D : Nat) (tailState endState : S)
    (hlen : N = T+D)
    (hprefix : run T (some (5,0,1)) = some tailState)
    (hend : run N (some (5,0,1)) = some endState)
    (hsafe : ∀ i, i ≤ D → ∀ t, run i (some tailState) = some t → ¬thinS t)
    (hd : 5 ≤ D) (hr : 11 ≤ rank endState)
    (j : Nat) (hj : j ≤ maxSafeIndex D endState) :
    ¬ ∃ n, run n (some (5,0,1)) = some (0,2*j,4*j+10) := by
  exact gateway_exclusion_from_safe_tail N T D (maxSafeIndex D endState)
    tailState endState hlen hprefix hend hsafe
    (by
      intro k hk
      have hle : k ≤ (D-5)/4 :=
        Nat.le_trans hk (Nat.min_le_left _ _)
      omega)
    (by
      intro k hk
      have hle : k ≤ (rank endState-11)/8 :=
        Nat.le_trans hk (Nat.min_le_right _ _)
      have hsub : rank endState-11+11=rank endState := Nat.sub_add_cancel hr
      have hnum : 8*k+11 ≤ rank endState := by omega
      simp only [rank] at hnum ⊢
      omega)
    j hj

/-- The two independent numeric constraints meet at the same ceiling
    for the certified endpoint; the current index 15742 is maximally
    extractable from this exact fixed safe-tail certificate. -/
theorem maxSafeIndex_at_witness : maxSafeIndex 62973 (2,62973,0) = 15742 := by
  decide

/-- Instantiation of the reusable theorem on the formal 567M-step trace. -/
theorem gateway_exclusion_instantiated (j : Nat) (hj : j ≤ 15742) :
    ¬∃n, run n (some (5,0,1)) = some (0,2*j,4*j+10) := by
  exact gateway_exclusion_from_safe_tail
    567323514 567260541 62973 15742 (2,31482,62976) (2,62973,0)
    (by decide) blank_tail_start blank_reaches_a2_c0 blank_tail_safe
    (by intro j hj; omega)
    (by intro j hj; simp only [rank]; omega) j hj

#print axioms gateway_exclusion_optimal_bound
#print axioms maxSafeIndex_at_witness
#print axioms gateway_exclusion_from_safe_tail
#print axioms gateway_exclusion_instantiated
end BB6Agent38
