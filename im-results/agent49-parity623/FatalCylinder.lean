import Std

/-! Generic ternary fatal cylinders, and intersection with arbitrary positive
arithmetic periods, from the four exact flat-drain backward rules. -/
namespace BB6.Agent49FatalCylinder

structure Rules (F : Nat → Nat → Prop) : Prop where
  zero : ∀ q, F 0 (3*q+1)
  lift0 : ∀ a b, F (a+1) b → F a (3*(b+1))
  lift1 : ∀ a b, F a b → F (a+1) (3*b+1)
  lift2 : ∀ a b, 0<b → F a b → F (a+1) (3*(b-1)+2)

def Ray (F : Nat → Nat → Prop) (a b e : Nat) : Prop :=
  ∀ t : Nat, F a (b+3^e*t)

theorem ray_shift {F : Nat → Nat → Prop} {a b e : Nat}
    (h : Ray F a b e) (s : Nat) : Ray F a (b+3^e*s) e := by
  intro t
  simpa [Nat.mul_add,Nat.add_assoc] using h (s+t)

theorem ray_lift0 {F : Nat → Nat → Prop} (R : Rules F) {a b e : Nat}
    (h : Ray F (a+1) b e) : Ray F a (3*(b+1)) (e+1) := by
  intro t
  have he : 3^(e+1)*t = 3*(3^e*t) := by
    rw [Nat.pow_succ, Nat.mul_comm (3^e) 3, Nat.mul_assoc]
  rw [he]
  have hx : 3*(b+1)+3*(3^e*t)=3*((b+3^e*t)+1) := by omega
  rw [hx]
  exact R.lift0 a (b+3^e*t) (h t)

theorem ray_lift1 {F : Nat → Nat → Prop} (R : Rules F) {a b e : Nat}
    (h : Ray F a b e) : Ray F (a+1) (3*b+1) (e+1) := by
  intro t
  have he : 3^(e+1)*t = 3*(3^e*t) := by
    rw [Nat.pow_succ, Nat.mul_comm (3^e) 3, Nat.mul_assoc]
  rw [he]
  have hx : 3*b+1+3*(3^e*t)=3*(b+3^e*t)+1 := by omega
  rw [hx]
  exact R.lift1 a (b+3^e*t) (h t)

theorem ray_lift2 {F : Nat → Nat → Prop} (R : Rules F) {a b e : Nat}
    (hb : 0<b) (h : Ray F a b e) : Ray F (a+1) (3*(b-1)+2) (e+1) := by
  intro t
  have he : 3^(e+1)*t = 3*(3^e*t) := by
    rw [Nat.pow_succ, Nat.mul_comm (3^e) 3, Nat.mul_assoc]
  rw [he]
  have hx : 3*(b-1)+2+3*(3^e*t)=3*((b+3^e*t)-1)+2 := by omega
  rw [hx]
  exact R.lift2 a (b+3^e*t) (by omega) (h t)

def first : Nat → Nat
  | 0 => 1
  | a+1 => 3*first a+1

theorem first_ray {F : Nat → Nat → Prop} (R : Rules F) (a : Nat) :
    Ray F a (first a) (a+1) := by
  induction a with
  | zero =>
    intro t
    change F 0 (1+3^1*t)
    rw [Nat.pow_one,Nat.add_comm]
    exact R.zero t
  | succ a ih => exact ray_lift1 R ih

/-- Every ternary prefix can be extended to a full fatal cylinder, provided
that the initial first counter is at least the prescribed prefix length.
The exponent of the resulting cylinder is at most a + 2*v + 1. -/
theorem fatal_prefix {F : Nat → Nat → Prop} (R : Rules F) (v : Nat) :
    ∀ a r : Nat, v≤a →
      ∃ n e : Nat, v+1≤e ∧ e≤a+2*v+1 ∧ Ray F a (r+3^v*n) e := by
  induction v with
  | zero =>
    intro a r _
    have hp : 1≤3^(a+1) := Nat.pow_pos (by decide)
    have hr : r≤first a+3^(a+1)*r := by
      have h := Nat.mul_le_mul_right r hp
      omega
    refine ⟨first a+3^(a+1)*r-r,a+1,by omega,by omega,?_⟩
    have he : r+3^0*(first a+3^(a+1)*r-r)=first a+3^(a+1)*r := by simp; omega
    rw [he]
    exact ray_shift (first_ray R a) r
  | succ v ih =>
    intro a r ha
    let p := 3^v
    let q := r/3+2*p
    have hp : 0<p := Nat.pow_pos (by decide)
    have hq : 1≤q := by dsimp [q]; omega
    have hpow : 3^(v+1)=3*p := by simp [p,Nat.pow_succ,Nat.mul_comm]
    have hrep : r+3*p*2=3*q+r%3 := by dsimp [q]; omega
    by_cases h0 : r%3=0
    · obtain ⟨n,e,he1,he2,hh⟩ := ih (a+1) (q-1) (by omega)
      have h := ray_lift0 R hh
      refine ⟨n+2,e+1,by omega,by omega,?_⟩
      have he : r+3^(v+1)*(n+2)=3*((q-1)+3^v*n+1) := by
        rw [hpow]
        change r+3*p*(n+2)=3*((q-1)+p*n+1)
        simp only [Nat.mul_add,Nat.mul_assoc]
        omega
      rw [he]
      exact h
    · have ha1 : a-1+1=a := by omega
      by_cases h1 : r%3=1
      · obtain ⟨n,e,he1,he2,hh⟩ := ih (a-1) q (by omega)
        have h := ray_lift1 R hh
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
        obtain ⟨n,e,he1,he2,hh⟩ := ih (a-1) (q+1) (by omega)
        have h := ray_lift2 R (by omega) hh
        rw [ha1] at h
        refine ⟨n+2,e+1,by omega,by omega,?_⟩
        have he : r+3^(v+1)*(n+2)=3*((q+1+3^v*n)-1)+2 := by
          rw [hpow]
          change r+3*p*(n+2)=3*((q+1+p*n)-1)+2
          simp only [Nat.mul_add,Nat.mul_assoc]
          omega
        rw [he]
        exact h

theorem factor_three (p : Nat) (hp : 0<p) :
    ∃ v m : Nat, p=3^v*m ∧ 0<m ∧ m%3≠0 := by
  induction p using Nat.strongRecOn with
  | ind p ih =>
    by_cases h : p%3=0
    · have hq : 0<p/3 := by omega
      have hlt : p/3<p := by omega
      obtain ⟨v,m,hm,hm0,hm3⟩ := ih (p/3) hlt hq
      refine ⟨v+1,m,?_,hm0,hm3⟩
      rw [Nat.pow_succ]
      have he : p=3*(p/3) := by omega
      rw [he,hm]
      ac_rfl
    · exact ⟨0,p,by simp,hp,h⟩

theorem inverse_three (m : Nat) (hm : m%3≠0) :
    ∃ u w : Nat, 3*u=1+m*w := by
  by_cases h : m%3=1
  · refine ⟨(2*m+1)/3,2,?_⟩
    omega
  · refine ⟨(m+1)/3,1,?_⟩
    omega

theorem inverse_three_power (m k : Nat) (hm : m%3≠0) :
    ∃ u w : Nat, 3^k*u=1+m*w := by
  induction k with
  | zero => exact ⟨1,0,by simp⟩
  | succ k ih =>
    obtain ⟨u,w,hu⟩ := ih
    obtain ⟨u0,w0,hu0⟩ := inverse_three m hm
    refine ⟨u*u0,w+w0+m*w*w0,?_⟩
    calc
      3^(k+1)*(u*u0) = (3^k*u)*(3*u0) := by rw [Nat.pow_succ]; ac_rfl
      _ = (1+m*w)*(1+m*w0) := by rw [hu,hu0]
      _ = 1+m*(w+w0+m*w*w0) := by
        simp only [Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one]
        ac_rfl

/-- Every arithmetic progression has a fatal member when the first counter
is at least the 3-adic valuation of its positive period. No CRT oracle. -/
theorem fatal_progression_factored {F : Nat → Nat → Prop} (R : Rules F)
    (v m a r : Nat) (hm : 0<m) (hm3 : m%3≠0) (ha : v≤a) :
    ∃ j, F a (r+(3^v*m)*j) := by
  obtain ⟨n,e,he,_,hRay⟩ := fatal_prefix R v a r ha
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

theorem le_three_pow (v : Nat) : v≤3^v := by
  induction v with
  | zero => simp
  | succ v ih =>
    have hpos : 0<3^v := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega

/-- A simple uniform sufficient budget on the first counter: a >= p. -/
theorem fatal_progression {F : Nat → Nat → Prop} (R : Rules F)
    (p a r : Nat) (hp : 0<p) (ha : p≤a) : ∃ j, F a (r+p*j) := by
  obtain ⟨v,m,hp',hm,hm3⟩ := factor_three p hp
  have hv := le_three_pow v
  have hmul := Nat.mul_le_mul_left (3^v) (show 1≤m by omega)
  simp only [Nat.mul_one] at hmul
  have hva : v≤a := by omega
  rw [hp']
  exact fatal_progression_factored R v m a r hm hm3 hva

#print axioms fatal_prefix
#print axioms fatal_progression
end BB6.Agent49FatalCylinder
