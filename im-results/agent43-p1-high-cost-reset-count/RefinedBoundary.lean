import ReverseGuard
import EvenQuarter
namespace BB6.Agent43RefinedBoundary
open BB6.Agent1Quarter BB6.Agent47P1 BB6.P1Reduction BB6.P1CarryExact
open BB6.Agent43LagExact BB6.Agent43LagBoundary BB6.Agent43P1Reverse

/-- Retain the authentic reset origin of an even feeder instead of dropping
it once the dyadic left coordinate has been derived. -/
def RefinedBoundary (n m v w : Nat) : Prop :=
  (w=6 ∨ w=7 ∨ w=8 ∨ w=10) ∨
  (v=2 ∧ (n+m)%2=0) ∨
  (5≤v ∧ v%2=1 ∧ ∃ j s, j<n ∧
    w+v/2=7*2^j ∧ s+2*j+13=14*2^j+v ∧
    BB6.Agent1.Reach 2 s ∧
    ((s%4=2 ∧ BB6.Agent1.Reach (s-6) 3) ∨ (j%4=1 ∧ v=2*j+5)))

private theorem linear_power (j : Nat) : 2*j+4<7*2^j := by
  induction j with
  | zero => decide
  | succ j ih => rw [Nat.pow_succ]; omega

/-- In the residue-zero case the earlier reset has precisely the same
dyadic exponent, which must be one modulo four. -/
theorem seed_refinement (j v w s : Nat) (hv : 5≤v) (ho : v%2=1)
    (hw : 6≤w) (hpow : w+v/2=7*2^j)
    (hs : s+2*j+13=14*2^j+v)
    (hr : BB6.Agent1.Reach 2 s) :
    (s%4=2 ∧ BB6.Agent1.Reach (s-6) 3) ∨ (j%4=1 ∧ v=2*j+5) := by
  have hj : 1≤j := by
    by_cases h0 : j=0
    · subst j; simp at hpow; omega
    · omega
  have hp : 2≤2^j := by
    have hp' := Nat.pow_le_pow_right (show 0<2 by decide) hj
    simpa using hp'
  have hl := linear_power j
  have hs12 : 12≤s := by omega
  have hse : s%2=0 := by omega
  by_cases hmod : s%4=0
  · obtain ⟨t,ht,htodd⟩ := BB6.Agent1.reset_divfour_one_mod_four s hr hs12 hmod
    have hlo : 7*2^j<s+8 := by omega
    have hhi : s+8<28*2^j := by omega
    have heq : t=j := by
      by_cases hlt : t<j
      · have hle : t+1≤j := by omega
        have hp' := Nat.pow_le_pow_right (show 0<2 by decide) hle
        rw [Nat.pow_succ] at hp'
        omega
      · by_cases hgt : j<t
        · have hle : j+1≤t := by omega
          have hp' := Nat.pow_le_pow_right (show 0<2 by decide) hle
          rw [Nat.pow_succ] at hp'
          omega
        · omega
    subst t
    exact Or.inr ⟨htodd,by omega⟩
  · have htwo : s%4=2 := by omega
    exact Or.inl ⟨htwo, BB6.Agent50P1.critical_target_implies_three s (by omega) htwo hr⟩

theorem right_five_refined (n b d m t k : Nat) (hn : 14≤n)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb : 12≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t=some (k,1))
    (hr : BB6.Agent1.Reach (2*k-2) 5) :
    ∃ b' d' m', 0<m' ∧ OddCone (criticalLeft n) 3 b' d' m' ∧
      RefinedBoundary n m' ((d'-1)/2) ((b'+12)/2) := by
  have hk := inverse_k_lower b d t k 1 hi
  have hchild := OddCone.parent b d m t k 1 h (by omega) hb4 hd hi (by omega) (by decide)
  have hL := source_to_legal n _ _ _ hn hchild
  have hm := legal_mass n _ _ _ hn hL
  have hpar := BB6.Agent1.reachable_even_mod4 (2*k-2) 5 hr (by decide) (by omega)
  have hT : total n%2=0 := by
    have he : 2∣2^n := Nat.pow_dvd_pow 2 (show 1≤n by omega)
    obtain ⟨a,ha⟩ := he
    unfold total
    rw [ha]
    omega
  refine ⟨2*k-4,5,m+t+1,by omega,hchild,?_⟩
  unfold RefinedBoundary
  rcases hpar with hp|hp
  · exact Or.inl (Or.inl (by omega))
  · exact Or.inr (Or.inl ⟨by decide,by omega⟩)

theorem even_feeder_refined (n b d m t k c : Nat) (hn : 14≤n)
    (h : OddCone (criticalLeft n) 3 b d m)
    (hb : 12≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t=some (k,c)) (hc : c%2=0) (hpos : 2≤c)
    (hreach : BB6.Agent1.Reach (2*k-4) (c+4)) :
    ∃ b' d' m', 0<m' ∧ OddCone (criticalLeft n) 3 b' d' m' ∧
      RefinedBoundary n m' ((d'-1)/2) ((b'+12)/2) := by
  have hlarge := pow2_ge_1100_mul n hn
  have hmass := odd_cone_mass _ _ b d m h
  unfold criticalLeft at hmass
  have hk := inverse_k_lower b d t k c hi
  obtain ⟨j,s,hrs,hj,hseed⟩ := BB6.Agent1.even_hub_reset_seed (2*k-4) (c+4)
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
    have hpow : k0+4+(c+3)/2=7*2^j := by omega
    have hs : s+2*j+13=14*2^j+(c+3) := by omega
    have href := seed_refinement j (c+3) (k0+4) s
      (by omega) (by omega) (by omega) hpow hs hrs
    exact Or.inr (Or.inr ⟨by omega,by omega,j,s,hlt,hpow,hs,hrs,href⟩)

/-- No margin, cutoff or extinction premise is needed. -/
theorem critical_hub_has_refined (n : Nat) (hn : 14≤n)
    (hr : BB6.Agent1.Reach (criticalLeft n) 3) :
    ∃ b d m, 0<m ∧ OddCone (criticalLeft n) 3 b d m ∧
      RefinedBoundary n m ((d-1)/2) ((b+12)/2) := by
  have hlarge := pow2_ge_1100_mul n hn
  have hrootEven : criticalLeft n%2=0 := by unfold criticalLeft; omega
  have hrootLarge : 12≤criticalLeft n := by unfold criticalLeft; omega
  have aux : ∀ fuel b d m : Nat, fuel=total n-m →
      OddCone (criticalLeft n) 3 b d m → BB6.Agent1.Reach b d →
      ∃ b' d' m', 0<m' ∧ OddCone (criticalLeft n) 3 b' d' m' ∧
        RefinedBoundary n m' ((d'-1)/2) ((b'+12)/2) := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro b d m hf h hre
      have hL := source_to_legal n b d m hn h
      have hmass := legal_mass n m _ _ hn hL
      have hbe := source_even_left _ _ _ _ _ hrootEven h
      have hdo := source_odd_right _ _ _ _ _ (by decide) h
      have hpar := BB6.Agent1.reachable_even_mod4 b d hre (by omega) hbe
      by_cases hb : b<12
      · have hmpos : 0<m := by cases h <;> omega
        exact ⟨b,d,m,hmpos,h,Or.inl (by rcases hpar with hp|hp <;> omega)⟩
      have hb4 : b%4=0 := by
        rcases BB6.Agent1.reachable_even_mod4 b d hre (by omega) hbe with h2|h4
        · omega
        · exact h4
      rcases actual_G_feeder b d (by omega) hb4 (by omega) hre with
        ⟨k,ha,hprev⟩ | ⟨k,c,ha,hpos,hpre⟩
      · obtain ⟨t,hi,_⟩ := inverseAt_complete b d k 1 ha
        exact right_five_refined n b d m t k hn h (by omega) hb4 hdo hi hprev
      · obtain ⟨t,hi,_⟩ := inverseAt_complete b d k c ha
        by_cases hodd : c%2=1
        · have hk := inverse_k_lower b d t k c hi
          have hchild := OddCone.parent b d m t k c h (by omega) hb4 hdo hi (by omega) hodd
          have hL' := source_to_legal n _ _ _ hn hchild
          have hm' := legal_mass n _ _ _ hn hL'
          exact ih (total n-(m+t+1)) (by omega) _ _ _ rfl hchild hpre
        · exact even_feeder_refined n b d m t k c hn h (by omega) hb4 hdo hi (by omega) hpos hpre
  exact aux (total n) (criticalLeft n) 3 0 (by omega) OddCone.root hr

/-- Test the exceptional arithmetic endpoints directly on guarded words. -/
theorem critical_reset_requires_refined (n : Nat) (hn : 14≤n)
    (he : n%2=0) (hr : BB6.Agent1.Reach 2 (14*2^n-2*n-10)) :
    ∃ m v w, 0<m ∧ 6≤w ∧ backCheck n m v w=true ∧ RefinedBoundary n m v w := by
  have hlarge := pow2_ge_1100_mul n hn
  have hdiv : 4∣2^n := Nat.pow_dvd_pow 2 (show 2≤n by omega)
  obtain ⟨u,hu⟩ := hdiv
  let d := 14*2^n-2*n-10
  have hd : 10≤d := by dsimp [d]; omega
  have hm : d%4=2 := by dsimp [d]; rw [hu]; omega
  have hR := BB6.Agent50P1.critical_target_implies_three d hd hm hr
  have hEq : d-6=criticalLeft n := by unfold d criticalLeft; omega
  rw [hEq] at hR
  obtain ⟨b,d',m,hpos,hcone,hB⟩ := critical_hub_has_refined n hn hR
  have hL := source_to_legal n b d' m hn hcone
  have hc := (back_iff_legal n m ((d'-1)/2) ((b+12)/2) hn).mp hL
  exact ⟨m,_,_,hpos,by rcases hc.2 with h|h <;> omega,hc.1,hB⟩

#print axioms seed_refinement
#print axioms critical_reset_requires_refined
end BB6.Agent43RefinedBoundary
