import Agent49FatalCylinder
namespace BB6.Agent49FatalCylinder

structure FullRules (F : Nat → Nat → Prop) extends Rules F : Prop where
  lift2zero : ∀ b, F 0 b → F 0 (3*b+2)

theorem ray_lift2zero {F : Nat → Nat → Prop} (R : FullRules F) {b e : Nat}
    (h : Ray F 0 b e) : Ray F 0 (3*b+2) (e+1) := by
  intro t
  have he : 3^(e+1)*t=3*(3^e*t) := by
    rw [Nat.pow_succ,Nat.mul_comm (3^e) 3,Nat.mul_assoc]
  rw [he]
  have hx : 3*b+2+3*(3^e*t)=3*(b+3^e*t)+2 := by omega
  rw [hx]
  exact R.lift2zero _ (h t)

theorem ray_zero_one {F : Nat → Nat → Prop} (R : Rules F) (r e : Nat)
    (hr : r%3=1) (he : 1≤e) : Ray F 0 r e := by
  intro t
  have hpow : 3^e=3*3^(e-1) := by
    rw [←Nat.pow_one 3,←Nat.pow_add]
    congr 1
    omega
  rw [hpow,Nat.mul_assoc]
  have h : r+3*(3^(e-1)*t)=3*(r/3+3^(e-1)*t)+1 := by omega
  rw [h]
  exact R.zero _

/-- No lower bound on the initial first counter is needed. Even at zero,
residue 1 halts immediately and residue 2 descends with counter zero. -/
theorem fatal_prefix_all {F : Nat → Nat → Prop} (R : FullRules F) (v : Nat) :
    ∀ a r : Nat,
      ∃ n e : Nat, v+1≤e ∧ e≤a+2*v+1 ∧ Ray F a (r+3^v*n) e := by
  induction v with
  | zero =>
    intro a r
    exact fatal_prefix R.toRules 0 a r (by omega)
  | succ v ih =>
    intro a r
    let p := 3^v
    let q := r/3+2*p
    have hp : 0<p := Nat.pow_pos (by decide)
    have hq : 1≤q := by dsimp [q]; omega
    have hpow : 3^(v+1)=3*p := by simp [p,Nat.pow_succ,Nat.mul_comm]
    have hrep : r+3*p*2=3*q+r%3 := by dsimp [q]; omega
    by_cases h0 : r%3=0
    · obtain ⟨n,e,he1,he2,hh⟩ := ih (a+1) (q-1)
      have h := ray_lift0 R.toRules hh
      refine ⟨n+2,e+1,by omega,by omega,?_⟩
      have he : r+3^(v+1)*(n+2)=3*((q-1)+3^v*n+1) := by
        rw [hpow]
        change r+3*p*(n+2)=3*((q-1)+p*n+1)
        simp only [Nat.mul_add,Nat.mul_assoc]
        omega
      rw [he]
      exact h
    · by_cases h1 : r%3=1
      · by_cases ha0 : a=0
        · subst a
          refine ⟨0,v+2,by omega,by omega,?_⟩
          simpa using ray_zero_one R.toRules r (v+2) h1 (by omega)
        · have ha1 : a-1+1=a := by omega
          obtain ⟨n,e,he1,he2,hh⟩ := ih (a-1) q
          have h := ray_lift1 R.toRules hh
          rw [ha1] at h
          refine ⟨n+2,e+1,by omega,by omega,?_⟩
          have he : r+3^(v+1)*(n+2)=3*(q+3^v*n)+1 := by
            rw [hpow]
            change r+3*p*(n+2)=3*(q+p*n)+1
            simp only [Nat.mul_add,Nat.mul_assoc]
            omega
          rw [he]
          exact h
      · have h2 : r%3=2 := by omega
        by_cases ha0 : a=0
        · subst a
          obtain ⟨n,e,he1,he2,hh⟩ := ih 0 q
          have h := ray_lift2zero R hh
          refine ⟨n+2,e+1,by omega,by omega,?_⟩
          have he : r+3^(v+1)*(n+2)=3*(q+3^v*n)+2 := by
            rw [hpow]
            change r+3*p*(n+2)=3*(q+p*n)+2
            simp only [Nat.mul_add,Nat.mul_assoc]
            omega
          rw [he]
          exact h
        · have ha1 : a-1+1=a := by omega
          obtain ⟨n,e,he1,he2,hh⟩ := ih (a-1) (q+1)
          have h := ray_lift2 R.toRules (by omega) hh
          rw [ha1] at h
          refine ⟨n+2,e+1,by omega,by omega,?_⟩
          have he : r+3^(v+1)*(n+2)=3*((q+1+3^v*n)-1)+2 := by
            rw [hpow]
            change r+3*p*(n+2)=3*((q+1+p*n)-1)+2
            simp only [Nat.mul_add,Nat.mul_assoc]
            omega
          rw [he]
          exact h

/-- The CRT intersection argument applies without any counter budget. -/
theorem fatal_progression_all_factored {F : Nat → Nat → Prop} (R : FullRules F)
    (v m a r : Nat) (hm : 0<m) (hm3 : m%3≠0) :
    ∃ j, F a (r+(3^v*m)*j) := by
  obtain ⟨n,e,he,_,hRay⟩ := fatal_prefix_all R v a r
  obtain ⟨u,w,hu⟩ := inverse_three_power m (e-v) hm3
  let s := m*(n+1)-n
  have hn : n≤m*(n+1) := by
    have h := Nat.mul_le_mul_right (n+1) (show 1≤m by omega)
    simp only [Nat.one_mul] at h
    omega
  have hs : n+s=m*(n+1) := by dsimp [s]; omega
  have hp : 3^e=3^v*3^(e-v) := by rw [←Nat.pow_add]; congr 1; omega
  refine ⟨n+1+w*s,?_⟩
  have hEq : r+3^v*n+3^e*(u*s)=r+(3^v*m)*(n+1+w*s) := by
    calc
      r+3^v*n+3^e*(u*s) = r+3^v*(n+3^(e-v)*(u*s)) := by
        rw [hp]; simp only [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc]
      _ = r+3^v*(n+(1+m*w)*s) := by rw [←Nat.mul_assoc (3^(e-v)) u s,hu]
      _ = r+3^v*(m*(n+1+w*s)) := by
        have hh : n+(1+m*w)*s=m*(n+1+w*s) := by
          rw [Nat.add_mul,Nat.one_mul,←Nat.add_assoc,hs]
          simp only [Nat.mul_add,Nat.mul_assoc]
        rw [hh]
      _ = r+(3^v*m)*(n+1+w*s) := by rw [Nat.mul_assoc]
  rw [←hEq]
  exact hRay (u*s)

theorem fatal_progression_all {F : Nat → Nat → Prop} (R : FullRules F)
    (p a r : Nat) (hp : 0<p) : ∃ j, F a (r+p*j) := by
  obtain ⟨v,m,hp',hm,hm3⟩ := factor_three p hp
  rw [hp']
  exact fatal_progression_all_factored R v m a r hm hm3

#print axioms fatal_prefix_all
#print axioms fatal_progression_all
end BB6.Agent49FatalCylinder
