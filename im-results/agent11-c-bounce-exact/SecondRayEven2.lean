import SecondRayAllList
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11Ray
open BB6.Agent46

/-- At m = 2 mod 4, no high bounce depth exceeds s=m. -/
theorem even2_ray_exponent_bound (m s a : Nat)
    (hm : m%4=2)
    (h : 4^(m+1)*(3*m+4)=4^(s+1)*(a+3)) :
    s≤m := by
  by_cases hle:s≤m
  · exact hle
  have hlt:m+1≤s := by omega
  exfalso
  have hs:s+1=(m+1)+(s-m) := by omega
  have hsplit : 4^(s+1)=4^(m+1)*4^(s-m) := by
    rw [hs,Nat.pow_add]
  rw [hsplit] at h
  have hc : 3*m+4=4^(s-m)*(a+3) := by
    apply Nat.eq_of_mul_eq_mul_left (show 0<4^(m+1) from Nat.pow_pos (by decide))
    calc
      4^(m+1)*(3*m+4)=(4^(m+1)*4^(s-m))*(a+3) := h
      _ = 4^(m+1)*(4^(s-m)*(a+3)) := by ac_rfl
  have hsm: s-m=(s-m-1)+1 := by omega
  have hdiv4 : (4^(s-m)*(a+3))%4=0 := by
    have h : 4^(s-m)*(a+3)=4*(4^(s-m-1)*(a+3)) := by
      have hp : 4^(s-m)=4*(4^(s-m-1)) := by
        calc
          4^(s-m)=4^((s-m-1)+1) := by congr 1
          _ = 4*(4^(s-m-1)) := by rw [Nat.pow_succ]; ac_rfl
      rw [hp]
      ac_rfl
    rw [h]
    omega
  omega

theorem even2_ray_factor (m s a:Nat)
    (hm:m%4=2)
    (h:4^(m+1)*(3*m+4)=4^(s+1)*(a+3)) :
    s≤m ∧ a+3=4^(m-s)*(3*m+4) := by
  have hle:=even2_ray_exponent_bound m s a hm h
  constructor
  · exact hle
  · have he:m+1=(s+1)+(m-s) := by omega
    have hsplit:4^(m+1)=4^(s+1)*4^(m-s) := by
      rw [he,Nat.pow_add]
    rw [hsplit] at h
    have hc : 4^(m-s)*(3*m+4)=a+3 := by
      apply Nat.eq_of_mul_eq_mul_left (show 0<4^(s+1) from Nat.pow_pos (by decide))
      calc
        4^(s+1)*(4^(m-s)*(3*m+4))=(4^(s+1)*4^(m-s))*(3*m+4) := by ac_rfl
        _=4^(s+1)*(a+3) := h
    exact hc.symm

private theorem two_mod_four_gt_two_not_power_two (b n:Nat)
    (hb:b%4=2) (hbig:2<b) : b≠2^n := by
  intro h
  cases n with
  | zero => simp at h; omega
  | succ n =>
      cases n with
      | zero => simp at h; omega
      | succ n =>
          have hp : 2^(Nat.succ (Nat.succ n))=4*2^n := by
            rw [show Nat.succ (Nat.succ n)=n+2 by omega,Nat.pow_add]
            omega
          rw [hp] at h
          omega

theorem even2_D_not_pow_two (m e:Nat) (hm:m%4=2) :
    4^(m+1)*(3*m+4)≠2^e := by
  intro h
  have hf : 4^(m+1)=2^(2*(m+1)) := by
    calc
      4^(m+1)=(2^2)^(m+1) := by simp
      _ = 2^(2*(m+1)) := (Nat.pow_mul 2 2 (m+1)).symm
  rw [hf] at h
  have hb:(3*m+4)%4=2 := by omega
  have hbig:2<3*m+4 := by omega
  by_cases hle:e≤2*(m+1)
  · have hlepow:2^e≤2^(2*(m+1)) := Nat.pow_le_pow_right (by decide) hle
    have hbigmul : 2^(2*(m+1)) < 2^(2*(m+1))*(3*m+4) := by
      have hp : 0<2^(2*(m+1)) := Nat.pow_pos (by decide)
      have hh:=Nat.mul_lt_mul_of_pos_left (by omega : 1<3*m+4) hp
      simpa using hh
    omega
  · have he:2*(m+1)≤e := by omega
    have hsplit : 2^e=2^(2*(m+1))*2^(e-2*(m+1)) := by
      have heq : e=2*(m+1)+(e-2*(m+1)) := by omega
      calc
        2^e=2^(2*(m+1)+(e-2*(m+1))) := by congr 1
        _ = 2^(2*(m+1))*2^(e-2*(m+1)) := Nat.pow_add 2 _ _
    rw [hsplit] at h
    have hc:3*m+4=2^(e-2*(m+1)) :=
      Nat.eq_of_mul_eq_mul_left (show 0<2^(2*(m+1)) from Nat.pow_pos (by decide)) h
    exact two_mod_four_gt_two_not_power_two (3*m+4) (e-2*(m+1)) hb hbig hc

def even2Boundary (m:Nat) : Nat×Nat :=
  (3*m+1,rayD m-((15*m+18)/2))

theorem even2_boundary_edge (m:Nat) (hm:m%4=2) :
  secNext (even2Boundary m)=some (rayX m,rayY m) := by
  let a:=3*m+1
  let k:=rayD m-((15*m+18)/2)
  have hmp : 2≤m := by omega
  have hD : 12*m+16≤rayD m := by
    have hp:1≤4^m:=Nat.one_le_pow m 4 (by decide)
    have he:rayD m=4*(4^m*(3*m+4)) := by
      unfold rayD
      rw [Nat.pow_succ]
      ac_rfl
    have hmul : 3*m+4≤4^m*(3*m+4) := by
      simpa using Nat.mul_le_mul_right (3*m+4) hp
    rw [he]
    omega
  have hcut : 2*((15*m+18)/2)=15*m+18 := by omega
  have hcutD : (15*m+18)/2≤rayD m := by omega
  have hk : k+(15*m+18)/2=rayD m := by dsimp [k];omega
  have ha : 3≤a := by dsimp [a];omega
  have hhigh : a<2*k := by dsimp [a,k];omega
  have hp : rayD m=2^(2*m+2)*(a+3) := by
    have he : 2^(2*m+2)=4^(m+1) := by
      rw [show 2*m+2=2*(m+1) by omega,Nat.pow_mul]
    rw [he]
    dsimp [rayD,a]
  have hf:=rayFacts m
  have hcost : 2*k+a+7+3*(2*m+1)=rayX m+2*rayY m := by
    dsimp [a,k]
    omega
  apply (original_ray_parent_iff m a k).mpr
  right
  right
  exact ⟨ha,hhigh,2*m+1,by omega,hp,hcost⟩

theorem even2_high_shape (m a k:Nat) (hm:m%4=2)
    (h : ∃ n:Nat, n%2=1 ∧
     rayD m=2^(n+1)*(a+3) ∧
     2*k+a+7+3*n=rayX m+2*rayY m) :
    ∃ s:Nat, s≤m ∧ a+3=4^(m-s)*(3*m+4) ∧
      2*k+a+7+3*(2*s+1)=rayX m+2*rayY m := by
  obtain ⟨n,hn,hpow,hcost⟩:=h
  let s:=n/2
  have hns:n=2*s+1:=by dsimp [s];omega
  have h2p:2^(n+1)=4^(s+1) := by
    rw [hns,show 2*s+1+1=2*(s+1) by omega,Nat.pow_mul]
  rw [h2p] at hpow
  have hf := even2_ray_factor m s a hm hpow
  refine ⟨s,hf.1,hf.2,?_⟩
  rw [←hns]
  exact hcost

/-- Exhaustive original-section fibre at m=2 mod 4, including exactly one
    new boundary source beyond the old fan. -/
theorem original_even2_ray_fibre_iff (m a k:Nat) (hm:m%4=2) :
  secNext (a,k)=some (rayX m,rayY m) ↔
  (a+3=rayD m ∧ 2*k+2=rayY m) ∨
  (∃ s t:Nat, m=s+t+1 ∧
      a=FanArithmetic.p s t ∧ k=FanArithmetic.q s t) ∨
  (a,k)=even2Boundary m := by
  constructor
  · intro h
    have hq:=(original_ray_parent_iff m a k).mp h
    rcases hq with hd | he | hh
    · exact Or.inl hd
    · obtain ⟨_,_,n,hpow,_⟩:=he
      have heq : rayD m=2^(n+4) := by
        calc
          rayD m=2^n*16 := hpow
          _=2^(n+4) := by rw [Nat.pow_add]
      exact False.elim ((even2_D_not_pow_two m (n+4) hm) heq)
    · obtain ⟨ha,hhigh,n,hn,hpow,hcost⟩:=hh
      obtain ⟨s,hs,haeq,hcost'⟩ := even2_high_shape m a k hm ⟨n,hn,hpow,hcost⟩
      by_cases hlt:s<m
      · let t:=m-s-1
        have hst:m=s+t+1:=by dsimp [t];omega
        have hta:t+1=m-s:=by dsimp [t];omega
        have hA:a+3=4^(t+1)*(3*m+4) := by rw [hta];exact haeq
        have hA2:a+3=4*(4^t*(3*m+4)) := by
          rw [hA,Nat.pow_succ]
          ac_rfl
        have hD:6*m+6≤rayD m := by
          have hf:=rayFacts m
          omega
        have hk': k+(2*4^t*(3*m+4)+3*m+7+3*s)=rayD m := by
          have hpp:2*4^t*(3*m+4)=2*(4^t*(3*m+4)) := by ac_rfl
          rw [hpp]
          have hfact := (rayFacts m).2.1
          dsimp [rayX] at hcost'
          omega
        obtain ⟨ha',hk'⟩ := fan_from_normalized m s t a k hst hA hk'
        right
        left
        exact ⟨s,t,hst,ha',hk'⟩
      · have hsm:s=m:=by omega
        have hA : a=3*m+1 := by
          have hh : a+3=3*m+4 := by simpa [hsm] using haeq
          omega
        have hcut : 2*((15*m+18)/2)=15*m+18 := by omega
        have hD : (15*m+18)/2≤rayD m := by
          have hf:=rayFacts m
          have hs: 6*m+6≤rayD m := by omega
          have hp:1≤4^m:=Nat.one_le_pow m 4 (by decide)
          have he:rayD m=4*(4^m*(3*m+4)) := by
            unfold rayD; rw [Nat.pow_succ];ac_rfl
          have hmul:3*m+4≤4^m*(3*m+4) := by
            simpa using Nat.mul_le_mul_right (3*m+4) hp
          have h12:12*m+16≤rayD m := by rw [he];omega
          omega
        have hK : k=rayD m-((15*m+18)/2) := by
          have hf:=(rayFacts m).2.1
          dsimp [rayX] at hcost'
          omega
        right
        right
        exact Prod.ext hA hK
  · rintro (hd | ⟨s,t,hst,ha,hk⟩ | hb)
    · exact (original_ray_parent_iff m a k).mpr (Or.inl hd)
    · have hedge:=BB6.Agent11Research.second_gate_incoming_edge s t
      have hsm:FanArithmetic.m s t=m := by dsimp [FanArithmetic.m];omega
      have hx:FanArithmetic.x s t=rayX m := by
        dsimp [FanArithmetic.x,rayX];rw [hsm]
      have hy:FanArithmetic.y s t=rayY m := by
        dsimp [FanArithmetic.y,rayY,rayD,FanArithmetic.d]
        rw [hsm]
        simp only [FanArithmetic.b]
        rw [hsm]
      have ht:secNext (FanArithmetic.p s t,FanArithmetic.q s t)=
          some (rayX m,rayY m) := by simpa only [hx,hy] using hedge
      simpa only [ha,hk] using ht
    · cases Prod.mk.inj hb with
      | intro ha hk =>
          subst a
          subst k
          exact even2_boundary_edge m hm

#print axioms original_even2_ray_fibre_iff
#print axioms even2_ray_factor
end BB6.Agent11Ray
