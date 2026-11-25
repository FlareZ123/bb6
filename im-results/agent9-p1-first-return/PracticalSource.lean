import BoundarySource

/-! Pointwise source barrier valid throughout the currently unresolved
critical-index range, with an explicit first-crossing interval. -/
namespace BB6.Agent9FirstReturn
open BB6.Agent1Quarter BB6.Agent47P1 BB6P1Unit BB6.P1CarryExact BB6.P1Reduction BB6.Agent9Renewal
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 20000

/-- Positive inverse inputs have tighter depth than the unconditional bound. -/
theorem critical_positive_inverse_depth (n b d m t k c : Nat) (hn : 8000≤n)
    (hc : OddCone (criticalLeft n) 3 b d m) (hpos : 1≤c)
    (hi : inverseAt b d t=some (k,c)) : t+1≤n+2 := by
  have hP := large_power n hn
  have hmass := odd_cone_mass _ _ b d m hc
  unfold criticalLeft at hmass
  have hp := inverseAt_power b d t k c hi
  by_cases ht : t≤n+1
  · omega
  · have ht' := Nat.pow_le_pow_right (show 0<2 by decide) (show n+2≤t by omega)
    rw [show 2^(n+2)=4*2^n by rw [Nat.pow_add]; simp; omega] at ht'
    have hmul := Nat.mul_le_mul_left (2^t) (show 4≤c+3 by omega)
    rw [←hp] at hmul
    omega

/-- The two-boundary estimate is already available at all n≥8000 for
histories of cost at most 4n. The threshold is a kernel-computed constant. -/
theorem practical_short_margins (n b d m : Nat) (hn : 8000≤n) (hm : m≤4*n)
    (hc : OddCone (criticalLeft n) 3 b d m) :
    (0<m → 128*n+1<d) ∧ 64*n<b/2+6 := by
  have ht : smallThreshold 4 64 8 1≤8000 := by decide
  have hs := source_short_margins 4 64 1 n b d m hn (by decide) (by decide) (Nat.le_trans ht hn) hm hc
  simpa using hs

def practicalCut (n : Nat) : Nat := 3*n+fourthPrefix n

theorem practical_reachable_child (n b d m : Nat) (hn : 8000≤n)
    (hm : m≤practicalCut n) (hc : OddCone (criticalLeft n) 3 b d m)
    (hr : BB6.Agent1.Reach b d) :
    ∃ b' d' m', OddCone (criticalLeft n) 3 b' d' m' ∧ BB6.Agent1.Reach b' d' ∧ m<m' ∧ m'≤m+n+2 := by
  have hP := large_power n hn
  have hroot : criticalLeft n+10=2*(7*2^n-n-3) := by unfold criticalLeft; omega
  obtain ⟨v,hd,hmass,hg⟩ := gap_of_oddcone _ _ b d m hroot hc
  have hK : fourthPrefix n≤n := by unfold fourthPrefix; omega
  have hm4 : m≤4*n := by unfold practicalCut at hm; omega
  have hleft := (practical_short_margins n b d m hn hm4 hc).2
  have hb : b%2=0 := by omega
  have hdodd : d%2=1 := by omega
  have hb4 : b%4=0 := by
    rcases BB6.Agent1.reachable_even_mod4 b d hr (by omega) hb with he|he
    · omega
    · exact he
  have hno : ∀ k, ¬GAncestor b d k 1 := by
    intro k ha
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
    have hk := ancestor_k_lower b d k 1 ha
    have ht := critical_positive_inverse_depth n b d m t k 1 hn hc (by decide) hi
    have hchild := OddCone.parent b d m t k 1 hc (by omega) hb4 hdodd hi (by omega) (by decide)
    have hs := source_right_five_cost_four_prefix n (2*k-4) (m+t+1) hn hchild
    unfold practicalCut at hm
    omega
  obtain ⟨k,c,ha,hc2,hpre⟩ := BB6.Agent50P1.positive_G_feeder b d (by omega) hb4 (by omega) hno hr
  obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
  have hk := ancestor_k_lower b d k c ha
  have ht := critical_positive_inverse_depth n b d m t k c hn hc (by omega) hi
  by_cases hodd : c%2=1
  · exact ⟨2*k-4,c+4,m+t+1,OddCone.parent b d m t k c hc (by omega) hb4 hdodd hi (by omega) hodd,hpre,by omega,by omega⟩
  · have hce : c%2=0 := by omega
    have hMass := odd_cone_mass _ _ b d m hc
    unfold criticalLeft at hMass
    have hback := inverseAt_exact_mass b d t k c (by omega) hb4 hdodd hi
    have hpower := inverseAt_power b d t k c hi
    have htp : 1≤t := by
      by_cases h0 : t=0
      · subst t; simp at hpower; omega
      · omega
    have hpow : 2≤2^t := Nat.pow_le_pow_right (show 0<2 by decide) htp
    have hcBound : 2*(c+3)≤d+b/2+3 := by rw [hpower]; exact Nat.mul_le_mul_right _ hpow
    have hl : 7*2^n<2*k+8 := by omega
    have hh : 2*k+8<14*2^n := by omega
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (2*k-4) (c+4) hpre (by omega) (by omega) (by omega)
    have hj' : 2*k+8=14*2^j := by omega
    exfalso
    by_cases hnJ : n≤j
    · have hjpow := Nat.pow_le_pow_right (show 0<2 by decide) hnJ
      omega
    · have hjpow := Nat.pow_le_pow_right (show 0<2 by decide) (show j≤n-1 by omega)
      have he : 2^n=2*2^(n-1) := by
        have hEq : n=n-1+1 := by omega
        calc
          2^n=2^(n-1+1) := congrArg (fun i : Nat => 2^i) hEq
          _=2*2^(n-1) := by rw [Nat.pow_succ]; ac_rfl
      omega

/-- A first crossing of a source cost cutoff must lie within the maximal
single-edge overshoot, retaining authentic blank reachability. -/
theorem reachable_first_crossing (n M delta : Nat)
    (hstep : ∀ b d m, m≤M → OddCone (criticalLeft n) 3 b d m → BB6.Agent1.Reach b d →
      ∃ b' d' m', OddCone (criticalLeft n) 3 b' d' m' ∧ BB6.Agent1.Reach b' d' ∧ m<m' ∧ m'≤m+delta)
    (hr : BB6.Agent1.Reach (criticalLeft n) 3) :
    ∃ b d m, OddCone (criticalLeft n) 3 b d m ∧ BB6.Agent1.Reach b d ∧ M<m ∧ m≤M+delta := by
  have aux : ∀ fuel b d m : Nat, M+1≤m+fuel → m≤M+delta → OddCone (criticalLeft n) 3 b d m → BB6.Agent1.Reach b d →
      ∃ b' d' m', OddCone (criticalLeft n) 3 b' d' m' ∧ BB6.Agent1.Reach b' d' ∧ M<m' ∧ m'≤M+delta := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro b d m hbudget hcap hc hre
      by_cases hlong : M<m
      · exact ⟨b,d,m,hc,hre,hlong,hcap⟩
      · obtain ⟨b',d',m',hc',hre',hm',hcap'⟩ := hstep b d m (by omega) hc hre
        exact ih (M+1-m') (by omega) b' d' m' (by omega) (by omega) hc' hre'
  exact aux (M+1) (criticalLeft n) 3 0 (by omega) (by omega) OddCone.root hr

theorem practical_critical_crossing (n : Nat) (hn : 8000≤n)
    (hr : BB6.Agent1.Reach (criticalLeft n) 3) :
    ∃ b d m, OddCone (criticalLeft n) 3 b d m ∧ BB6.Agent1.Reach b d ∧
      practicalCut n<m ∧ m≤practicalCut n+n+2 := by
  exact reachable_first_crossing n (practicalCut n) (n+2) (fun b d m hm hc h => by
    obtain ⟨b',d',m',hc',hr',hm',hcap⟩ := practical_reachable_child n b d m hn hm hc h
    exact ⟨b',d',m',hc',hr',hm',by omega⟩) hr

theorem practical_reset_crossing (n : Nat) (hn : 8000≤n) (he : n%2=0)
    (hr : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) :
    ∃ b d m, OddCone (criticalLeft n) 3 b d m ∧ BB6.Agent1.Reach b d ∧
      practicalCut n<m ∧ m≤practicalCut n+n+2 := by
  have hP := large_power n hn
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hdiv : 4∣2^n := Nat.pow_dvd_pow 2 (show 2≤n by omega)
  obtain ⟨u,hu⟩ := hdiv
  have hdmod : d%4=2 := by dsimp [d]; rw [hu]; omega
  have hre := BB6.Agent50P1.critical_target_implies_three d hd hdmod hr
  have hdroot : d-6=criticalLeft n := by unfold d criticalLeft; omega
  rw [hdroot] at hre
  exact practical_critical_crossing n hn hre

#print axioms critical_positive_inverse_depth
#print axioms practical_short_margins
#print axioms practical_reachable_child
#print axioms reachable_first_crossing
#print axioms practical_critical_crossing
#print axioms practical_reset_crossing
end BB6.Agent9FirstReturn
