import RenewalPrefixSource
import SmallComplement
import P1CarryBlankArithmetic
import P1Gate

/-! Original-source, two-boundary exclusion and a reachable long-history
necessity. The threshold does not assume a cap on all inverse histories. -/
namespace BB6.Agent9FirstReturn
open BB6.Agent1Quarter BB6.Agent47P1 BB6P1Unit BB6.P1CarryExact BB6.P1Reduction BB6.Agent9Renewal
set_option maxHeartbeats 2000000

/-- Both coordinates of every short critical cone endpoint, except the
right coordinate of the root itself, exceed any prescribed polynomial. -/
theorem source_short_margins (h B p n b d m : Nat)
    (hn : 8000≤n) (hB : 2≤B) (hp : 1≤p)
    (hdom : smallThreshold h B (h+4) p≤n) (hm : m≤h*n)
    (hc : OddCone (criticalLeft n) 3 b d m) :
    (0<m → 2*B*n^p+1<d) ∧ B*n^p<b/2+6 := by
  let Q := 7*2^n-n-3
  have hP := large_power n hn
  have hroot : criticalLeft n+10=2*Q := by unfold criticalLeft Q; omega
  obtain ⟨v,hd,hmass,hg⟩ := gap_of_oddcone _ Q b d m hroot hc
  have hbnd := gap_bounds hg
  have hvq : v<Q-m := by
    by_cases hm0 : m=0
    · have hv1 : v=1 := by cases hg <;> omega
      dsimp [Q]; omega
    · have hh := hbnd.2 (by omega)
      omega
  obtain ⟨hpath,hprefix⟩ := gap_reverse hg
  have hr := path_run hpath (by omega)
  have hclock : Q-m+m=7*2^n-n-3 := by dsimp [Q] at *; omega
  have hs := short_endpoint_margins h B p n (Q-m) v m hn hB hp hdom hclock hvq hm hprefix hr
  constructor
  · intro hmpos
    have hh := hs.1 hmpos
    have he : 2*B*n^p=2*(B*n^p) := by ac_rfl
    rw [he]; omega
  · have he : Q-m+2-v=b/2+6 := by omega
    rw [he] at hs
    exact hs.2

/-- Any inverseAt output from the critical cone has an elementary depth
bound, independent of the total cone cost. -/
theorem critical_inverse_depth (n b d m t k c : Nat) (hn : 8000≤n)
    (hc : OddCone (criticalLeft n) 3 b d m)
    (hi : inverseAt b d t=some (k,c)) : t+1≤2*n := by
  have hP := large_power n hn
  have hmass := odd_cone_mass _ _ b d m hc
  unfold criticalLeft at hmass
  have hp := inverseAt_power b d t k c hi
  by_cases ht : t≤n+3
  · omega
  · have ht' := Nat.pow_le_pow_right (show 0<2 by decide) (show n+4≤t by omega)
    rw [show 2^(n+4)=16*2^n by rw [Nat.pow_add]; simp; omega] at ht'
    have hmul := Nat.mul_le_mul_left (2^t) (show 1≤c+3 by omega)
    rw [Nat.mul_one,←hp] at hmul
    omega

/-- The finite threshold needed for all possible inverse outputs of every
short reachable node, including its at-most-2n-cost next odd child. -/
def reachableThreshold (h : Nat) : Nat :=
  max 8000 (smallThreshold (h+2) (6*h+46) (h+6) 1)

theorem short_node_margin (h n b d m : Nat) (hn : reachableThreshold h≤n)
    (hm : m≤h*n) (hc : OddCone (criticalLeft n) 3 b d m) :
    n+3*((h+2)*n+1)+10≤b/4 := by
  have hn8 : 8000≤n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hdom : smallThreshold (h+2) (6*h+46) ((h+2)+4) 1≤n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hm' : m≤(h+2)*n := by rw [Nat.add_mul]; omega
  have hs := (source_short_margins (h+2) (6*h+46) 1 n b d m hn8 (by omega) (by decide) hdom hm' hc).2
  simp only [Nat.pow_one,Nat.add_mul] at hs ⊢
  have he : 6*h*n=6*(h*n) := by ac_rfl
  rw [he] at hs
  omega

/-- A reachable short node must have a further reachable odd-cone
ancestor. The exceptional right-five and positive-even-power exits are
both excluded; the proof does not assume any global cost cap. -/
theorem short_reachable_child (h n b d m : Nat) (hn : reachableThreshold h≤n)
    (hm : m≤h*n) (hc : OddCone (criticalLeft n) 3 b d m)
    (hr : BB6.Agent1.Reach b d) :
    ∃ b' d' m', OddCone (criticalLeft n) 3 b' d' m' ∧ BB6.Agent1.Reach b' d' ∧ m<m' := by
  have hn8 : 8000≤n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hdom : smallThreshold (h+2) (6*h+46) ((h+2)+4) 1≤n := Nat.le_trans (Nat.le_max_right _ _) hn
  have hP := large_power n hn8
  have hroot : criticalLeft n+10=2*(7*2^n-n-3) := by unfold criticalLeft; omega
  obtain ⟨v,hd,hmass,hg⟩ := gap_of_oddcone _ _ b d m hroot hc
  have hleft := short_node_margin h n b d m hn hm hc
  have hb : b%2=0 := by omega
  have hdodd : d%2=1 := by omega
  have hb4 : b%4=0 := by
    rcases BB6.Agent1.reachable_even_mod4 b d hr hb hdodd with he|he
    · omega
    · exact he
  have hno : ∀ k, ¬GAncestor b d k 1 := by
    intro k ha
    obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
    have hk := ancestor_k_lower b d k 1 ha
    have ht := critical_inverse_depth n b d m t k 1 hn8 hc hi
    have hchild := OddCone.parent b d m t k 1 hc (by omega) hb4 hdodd hi (by omega) (by decide)
    have hcap : m+t+1≤(h+2)*n := by rw [Nat.add_mul]; omega
    have hs := (source_short_margins (h+2) (6*h+46) 1 n (2*k-4) 5 (m+t+1) hn8 (by omega) (by decide) hdom hcap hchild).1 (by omega)
    simp only [Nat.pow_one] at hs
    have hmul := Nat.mul_le_mul (show 2≤2*(6*h+46) by omega) hn8
    omega
  obtain ⟨k,c,ha,hc2,hpre⟩ := BB6.Agent50P1.positive_G_feeder b d (by omega) hb4 (by omega) hno hr
  obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
  have hk := ancestor_k_lower b d k c ha
  by_cases hodd : c%2=1
  · exact ⟨2*k-4,c+4,m+t+1,OddCone.parent b d m t k c hc (by omega) hb4 hdodd hi (by omega) hodd,hpre,by omega⟩
  · have hce : c%2=0 := by omega
    have ht := critical_inverse_depth n b d m t k c hn8 hc hi
    have hcost : m+t<(h+2)*n+1 := by rw [Nat.add_mul]; omega
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

/-- An authentic reachable critical root necessarily has an authentic
reachable ancestor at arbitrarily large fixed linear cost, once n is above
the corresponding explicit threshold. This strengthens the unrestricted
inverse-cone cost statement to actual source reachability. -/
theorem reachable_critical_has_long_cone (h n : Nat) (hn : reachableThreshold h≤n)
    (hr : BB6.Agent1.Reach (criticalLeft n) 3) :
    ∃ b d m, OddCone (criticalLeft n) 3 b d m ∧ BB6.Agent1.Reach b d ∧ h*n<m := by
  have aux : ∀ fuel b d m : Nat, h*n+1≤m+fuel → OddCone (criticalLeft n) 3 b d m → BB6.Agent1.Reach b d →
      ∃ b' d' m', OddCone (criticalLeft n) 3 b' d' m' ∧ BB6.Agent1.Reach b' d' ∧ h*n<m' := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro b d m hbudget hc hre
      by_cases hlong : h*n<m
      · exact ⟨b,d,m,hc,hre,hlong⟩
      · obtain ⟨b',d',m',hc',hre',hm'⟩ := short_reachable_child h n b d m hn (by omega) hc hre
        exact ih (h*n+1-m') (by omega) b' d' m' (by omega) hc' hre'
  exact aux (h*n+1) (criticalLeft n) 3 0 (by omega) OddCone.root hr

theorem reachable_reset_has_long_cone (h n : Nat) (hn : reachableThreshold h≤n) (he : n%2=0)
    (hr : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) :
    ∃ b d m, OddCone (criticalLeft n) 3 b d m ∧ BB6.Agent1.Reach b d ∧ h*n<m := by
  have hn8 : 8000≤n := Nat.le_trans (Nat.le_max_left _ _) hn
  have hP := large_power n hn8
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hdiv : 4∣2^n := Nat.pow_dvd_pow 2 (show 2≤n by omega)
  obtain ⟨u,hu⟩ := hdiv
  have hdmod : d%4=2 := by dsimp [d]; rw [hu]; omega
  have hre := BB6.Agent50P1.critical_target_implies_three d hd hdmod hr
  have hdroot : d-6=criticalLeft n := by unfold d criticalLeft; omega
  rw [hdroot] at hre
  exact reachable_critical_has_long_cone h n hn hre

#print axioms source_short_margins
#print axioms critical_inverse_depth
#print axioms short_node_margin
#print axioms short_reachable_child
#print axioms reachable_critical_has_long_cone
#print axioms reachable_reset_has_long_cone
end BB6.Agent9FirstReturn
