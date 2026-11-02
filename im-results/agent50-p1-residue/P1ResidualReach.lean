import ResetGate
import P1Triple
import P1ResidualArithmetic

namespace BB6.Agent50P1
open BB6.P1Reduction

/-- Independent bridge from Agent 1's exact G to the already certified finite G inverse relation. -/
theorem inverse_complete (k c b d : Nat) (h : BB6.Agent1.G k c=(b,d)) (hb : 0<b) :
    GAncestor b d k c := by
  induction k using Nat.strongRecOn generalizing c with
  | ind k ih =>
      by_cases hlow : c<2*k
      · rw [BB6.Agent1.G] at h
        simp only [hlow,dite_true] at h
        have child := ih (k-(c/2+1)) (by omega) (2*c+3) h
        have hk : k-(c/2+1)+c/2+1=k := by omega
        simpa only [hk] using GAncestor.nest b d (k-(c/2+1)) c child
      · by_cases hmid : c≤2*k+1
        · rw [BB6.Agent1.G] at h
          simp only [hlow,dite_false,hmid,ite_true] at h
          have he : b=0 := (Prod.mk.inj h).1.symm
          omega
        · have hc : 2*k+2≤c := by omega
          rw [BB6.Agent1.G] at h
          simp only [hlow,dite_false,hmid,ite_false] at h
          obtain ⟨hbeq,hdeq⟩ := Prod.mk.inj h
          have hbval : b=4*k+4 := hbeq.symm
          have hcval : c=d+2*k+2 := by omega
          subst b
          subst c
          exact GAncestor.upper k d

/-- For a positive multiple-of-four output excluding the c=3 exceptional input,
 every blank-reachable return has a positive even-left feeder. -/
theorem positive_G_feeder (b d : Nat) (hb : 8≤b) (hmod : b%4=0)
    (hd : 0<d) (hno : ∀ k, ¬GAncestor b d k 1)
    (hr : BB6.Agent1.Reach b d) :
    ∃ k v : Nat, GAncestor b d k v ∧ 2≤v ∧
      BB6.Agent1.Reach (2*k-4) (v+4) := by
  cases hr with
  | init => omega
  | next a c _ _ hpre ht =>
    unfold BB6.Agent1.T at ht
    by_cases hzero : c=0
    · simp [hzero] at ht
      omega
    · by_cases hone : c=1
      · simp [hzero,hone] at ht
        omega
      · by_cases haeven : a%2=0
        · simp [hzero,hone,haeven] at ht
          omega
        · by_cases htwo : c=2
          · simp [hzero,hone,haeven,htwo] at ht
          · by_cases hthree : c=3
            · simp [hzero,hone,haeven,htwo,hthree] at ht
              have ha : BB6.Agent1.G (a/2) 1=(b,d) := by
                simpa using ht
              have hf:=inverse_complete (a/2) 1 b d ha (by omega)
              exact False.elim (hno _ hf)
            · simp [hzero,hone,haeven,htwo,hthree] at ht
              have he : BB6.Agent1.G (a/2+1) (c-2)=(b,d) := by
                simpa using ht
              have hg := inverse_complete (a/2+1) (c-2) b d he (by omega)
              obtain ⟨x,y,hprev,hxe,hax,hy⟩:=
                BB6.Agent1.odd_parent_general a c hpre (by omega) (by omega)
              refine ⟨a/2+1,c-2,hg,by omega,?_⟩
              have heq : (2*(a/2+1)-4)=x := by omega
              have hceq : c-2+4=y := by omega
              simpa only [heq,hceq] using hprev

#print axioms inverse_complete
end BB6.Agent50P1

namespace BB6.Agent50P1
open BB6.P1Reduction

/-- Uniform global exclusion of the whole residual odd-sector subfamily,
provided the two relevant 14-power obstructions. -/
theorem residual_odd_hub_impossible (s : Nat)
    (hs : s%2=1) (hge : 3≤s)
    (h11 : ∀ j, 11*s+13 ≠ 14*2^j)
    (h13 : ∀ j, 13*s+15 ≠ 14*2^j) :
    ¬BB6.Agent1.Reach (16*s+12) 3 := by
  intro hr
  have hno0 : ∀ k, ¬GAncestor (16*s+12) 3 k 1 := by
    intro k h
    rcases inverse_16s12_three (16*s+12) 3 k 1 s h rfl rfl with
      h1 | h2 | h3 <;> omega
  obtain ⟨k,v,hanc,hv,hreach⟩ := positive_G_feeder
    (16*s+12) 3 (by omega) (by omega) (by omega) hno0 hr
  rcases inverse_16s12_three (16*s+12) 3 k v s hanc rfl rfl with
    h1 | h2 | h3
  · obtain ⟨hk,hv'⟩ := h1
    have hb : 2*k-4=8*s := by omega
    have hd : v+4=8*s+13 := by omega
    rw [hb,hd] at hreach
    have hno1 : ∀ z, ¬GAncestor (8*s) (8*s+13) z 1 := by
      intro z h
      rcases inverse_8s_splus13 (8*s) (8*s+13) z 1 s h rfl rfl hs hge with
        h1 | h2 | h3 <;> omega
    obtain ⟨z,w,hanc2,hw,hreach2⟩ := positive_G_feeder
      (8*s) (8*s+13) (by omega) (by omega) (by omega) hno1 hreach
    rcases inverse_8s_splus13 (8*s) (8*s+13) z w s hanc2 rfl rfl hs hge with
      g1 | g2 | g3
    · obtain ⟨hz,hw'⟩ := g1
      have hp : 2*z-4=4*s-6 := by omega
      have hq : w+4=12*s+17 := by omega
      rw [hp,hq] at hreach2
      have hm := BB6.Agent1.reachable_even_mod4 (4*s-6) (12*s+17) hreach2
        (by omega) (by omega)
      rcases hm with hh | hh <;> omega
    · obtain ⟨hz,hw'⟩ := g2
      have hp : 2*z-4=10*s := by omega
      have hq : w+4=6*s+9 := by omega
      rw [hp,hq] at hreach2
      have hm := BB6.Agent1.reachable_even_mod4 (10*s) (6*s+9) hreach2
        (by omega) (by omega)
      rcases hm with hh | hh <;> omega
    · obtain ⟨hz,hw'⟩ := g3
      have hp : 2*z-4=13*s+3 := by omega
      have hq : w+4=3*s+5 := by omega
      rw [hp,hq] at hreach2
      obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (13*s+3) (3*s+5)
        hreach2 (by omega) (by omega) (by omega)
      exact h13 j (by omega)
  · obtain ⟨hk,hv'⟩ := h2
    have hb : 2*k-4=12*s+4 := by omega
    have hd : v+4=4*s+7 := by omega
    rw [hb,hd] at hreach
    have hno1 : ∀ z, ¬GAncestor (12*s+4) (4*s+7) z 1 := by
      intro z h
      rcases inverse_12s4_4s7 (12*s+4) (4*s+7) z 1 s h rfl rfl hs with
        h1 | h2 <;> omega
    obtain ⟨z,w,hanc2,hw,hreach2⟩ := positive_G_feeder
      (12*s+4) (4*s+7) (by omega) (by omega) (by omega) hno1 hreach
    rcases inverse_12s4_4s7 (12*s+4) (4*s+7) z w s hanc2 rfl rfl hs with
      g1 | g2
    · obtain ⟨hz,hw'⟩ := g1
      have hp : 2*z-4=6*s-4 := by omega
      have hq : w+4=10*s+13 := by omega
      rw [hp,hq] at hreach2
      have hm := BB6.Agent1.reachable_even_mod4 (6*s-4) (10*s+13) hreach2
        (by omega) (by omega)
      rcases hm with hh | hh <;> omega
    · obtain ⟨hz,hw'⟩ := g2
      have hp : 2*z-4=11*s+1 := by omega
      have hq : w+4=5*s+7 := by omega
      rw [hp,hq] at hreach2
      obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (11*s+1) (5*s+7)
        hreach2 (by omega) (by omega) (by omega)
      exact h11 j (by omega)
  · obtain ⟨hk,hv'⟩ := h3
    have hp : 2*k-4=14*s+6 := by omega
    have hq : v+4=2*s+4 := by omega
    rw [hp,hq] at hreach
    obtain ⟨j,hj⟩ := BB6.Agent1.even_left_power_shape (14*s+6) (2*s+4)
      hreach (by omega) (by omega) (by omega)
    omega

/-- A genuine infinite subfamily of P1 residual odd-sector halting gateways is unreachable. -/
theorem blank_no_residual_critical_10_mod16 (k : Nat) :
    ¬BB6.Agent1.Reach (14*2^(16*k+10)-2*(16*k+10)-16) 3 := by
  rw [target_shape]
  exact residual_odd_hub_impossible (s k) (s_odd k) (s_ge_three k)
    (no_power_11 k) (no_power_13 k)

#print axioms residual_odd_hub_impossible
#print axioms blank_no_residual_critical_10_mod16
end BB6.Agent50P1
