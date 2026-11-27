import LagGuardedTrace
import P1CarryBlankArithmetic
import P1Gate

namespace BB6.Agent43LagBoundary
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction BB6.P1CarryExact
open BB6.Agent43LagExact

/-- A reachable critical hub requires a cone endpoint in one of these
three arithmetic sets. The even-power feeder is tested at its immediately
preceding odd depth. -/
def Boundary (n m v w : Nat) : Prop :=
  w≤11 ∨ v=2 ∨ (5≤v ∧ v%2=1 ∧ ∃ j, j<n ∧ w+v/2=7*2^j)

theorem even_feeder_boundary (n b d m t k c : Nat) (hn : 14≤n)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb : 12≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t=some (k,c)) (hc : c%2=0) (hpos : 2≤c)
    (hreach : BB6.Agent1.Reach (2*k-4) (c+4)) :
    ∃ b' d' m', 0<m' ∧ OddCone (criticalLeft n) 3 b' d' m' ∧
      Boundary n m' ((d'-1)/2) ((b'+12)/2) := by
  have hlarge := pow2_ge_1100_mul n hn
  have hmass := odd_cone_mass _ _ b d m h
  unfold criticalLeft at hmass
  have hk := inverse_k_lower b d t k c hi
  obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (2*k-4) (c+4)
      hreach (by omega) (by omega) (by omega)
  have hp := inverseAt_power b d t k c hi
  have hm := inverseAt_exact_mass b d t k c (by omega) hb4 hd hi
  have hj' : k+4=7*2^j := by omega
  have hlt : j<n := by
    by_cases hh : j<n
    · exact hh
    have hP := Nat.pow_le_pow_right (show 0<2 by decide) (show n≤j by omega)
    omega
  cases t with
  | zero => simp at hp; omega
  | succ t =>
    obtain ⟨k0,c0,hi0,hodd⟩ := inverse_prev_odd b d t k c hi
    have hk0 := inverse_k_lower b d t k0 c0 hi0
    have hp0 := inverseAt_power b d t k0 c0 hi0
    have hm0 := inverseAt_exact_mass b d t k0 c0 (by omega) hb4 hd hi0
    have heq : c0+3=2*(c+3) := by
      rw [Nat.pow_succ,Nat.mul_assoc] at hp
      exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos t) (hp0.symm.trans hp)
    refine ⟨2*k0-4,c0+4,m+t+1,by omega,
      OddCone.parent b d m t k0 c0 h (by omega) hb4 hd hi0 (by omega) hodd,?_⟩
    have hV : (c0+4-1)/2=c+3 := by omega
    have hW : (2*k0-4+12)/2=k0+4 := by omega
    rw [hV,hW]
    exact Or.inr (Or.inr ⟨by omega,by omega,j,hlt,by omega⟩)

/-- No margin, cutoff or extinction premise is needed. -/
theorem critical_hub_has_boundary (n : Nat) (hn : 14≤n)
    (hr : BB6.Agent1.Reach (criticalLeft n) 3) :
    ∃ b d m, 0<m ∧ OddCone (criticalLeft n) 3 b d m ∧
      Boundary n m ((d-1)/2) ((b+12)/2) := by
  have hlarge := pow2_ge_1100_mul n hn
  have hrootEven : criticalLeft n%2=0 := by unfold criticalLeft; omega
  have hrootLarge : 12≤criticalLeft n := by unfold criticalLeft; omega
  have aux : ∀ fuel b d m : Nat, fuel=total n-m →
      OddCone (criticalLeft n) 3 b d m → BB6.Agent1.Reach b d →
      ∃ b' d' m', 0<m' ∧ OddCone (criticalLeft n) 3 b' d' m' ∧
        Boundary n m' ((d'-1)/2) ((b'+12)/2) := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro b d m hf h hre
      have hL := source_to_legal n b d m hn h
      have hmass := legal_mass n m _ _ hn hL
      have hbe := source_even_left _ _ _ _ _ hrootEven h
      have hdo := source_odd_right _ _ _ _ _ (by decide) h
      by_cases hb : b<12
      · have hmpos : 0<m := by cases h <;> omega
        exact ⟨b,d,m,hmpos,h,Or.inl (by omega)⟩
      have hb4 : b%4=0 := by
        rcases BB6.Agent1.reachable_even_mod4 b d hre (by omega) hbe with h2|h4
        · omega
        · exact h4
      by_cases hx : ∃ k, GAncestor b d k 1
      · obtain ⟨k,ha⟩ := hx
        obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
        have hk := inverse_k_lower b d t k 1 hi
        exact ⟨2*k-4,5,m+t+1,by omega,
          OddCone.parent b d m t k 1 h (by omega) hb4 hdo hi (by omega) (by decide),
          Or.inr (Or.inl (by decide))⟩
      have hno : ∀ k, ¬ GAncestor b d k 1 := fun k hk => hx ⟨k,hk⟩
      obtain ⟨k,c,ha,hpos,hpre⟩ := BB6.Agent50P1.positive_G_feeder b d
        (by omega) hb4 (by omega) hno hre
      obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
      by_cases hodd : c%2=1
      · have hk := inverse_k_lower b d t k c hi
        have hchild := OddCone.parent b d m t k c h (by omega) hb4 hdo hi (by omega) hodd
        have hL' := source_to_legal n _ _ _ hn hchild
        have hm' := legal_mass n _ _ _ hn hL'
        exact ih (total n-(m+t+1)) (by omega) _ _ _ rfl hchild hpre
      · exact even_feeder_boundary n b d m t k c hn h (by omega) hb4 hdo hi (by omega) hpos hpre
  exact aux (total n) (criticalLeft n) 3 0 (by omega) OddCone.root hr

/-- Test the exceptional arithmetic endpoints directly on guarded words. -/
theorem critical_reset_requires_guarded_boundary (n : Nat) (hn : 14≤n)
    (he : n%2=0) (hr : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) :
    ∃ m B a, GuardedTrace n m B a ∧
      6≤leftAt n m B a ∧ Boundary n m (rightAt n m B a) (leftAt n m B a) := by
  have hlarge := pow2_ge_1100_mul n hn
  have hdiv : 4∣2^n := Nat.pow_dvd_pow 2 (show 2≤n by omega)
  obtain ⟨u,hu⟩ := hdiv
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hm : d%4=2 := by dsimp [d]; rw [hu]; omega
  have hR := BB6.Agent50P1.critical_target_implies_three d hd hm hr
  have hEq : d-6=criticalLeft n := by unfold d criticalLeft; omega
  rw [hEq] at hR
  obtain ⟨b,d',m,hpos,hcone,hB⟩ := critical_hub_has_boundary n hn hR
  have hL := source_to_legal n b d' m hn hcone
  obtain ⟨B,a,hT,hv,hw,hW⟩ := (legal_iff_guarded_trace n m _ _ hn he).mp ⟨hL,hpos⟩
  rw [hv,hw] at hB hW
  exact ⟨m,B,a,hT,hW,hB⟩

theorem low_boundary_wall (n m v w : Nat) (hmass : v+w+n+m+1=total n)
    (hw : 6≤w) (hshort : 2*(n+m)<total n+8)
    (h : Boundary n m v w) :
    w≤11 ∨ v=2 ∨ (5≤v ∧ v%2=1 ∧ w=n+m+2) := by
  rcases h with h|h|⟨hv,ho,j,hj,hpow⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · have heq : 2*w+v=14*2^j+1 := by omega
    by_cases hj' : j+1=n
    · have hT : total n=14*2^j := by unfold total; rw [←hj',Nat.pow_succ]; omega
      exact Or.inr (Or.inr ⟨hv,ho,by omega⟩)
    · have hJ : j+2≤n := by omega
      have hP := Nat.pow_le_pow_right (show 0<2 by decide) hJ
      rw [Nat.pow_add] at hP
      have h4 : (2:Nat)^2=4 := by decide
      rw [h4] at hP
      unfold total at *
      omega

#print axioms even_feeder_boundary
#print axioms critical_hub_has_boundary
#print axioms critical_reset_requires_guarded_boundary
#print axioms low_boundary_wall

end BB6.Agent43LagBoundary
