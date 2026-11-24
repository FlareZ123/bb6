import SheepEven

namespace SheepRawCylinder

def Generic (a x y : Nat) : Prop :=
  ∃ u, u % 2 = 1 ∧ 5 ≤ u ∧ x = 2^a*u ∧ y = x+a+(u-1)/2

theorem generic_source {a x y : Nat} (h : Generic a x y) : SheepEven.Step x y := by
  obtain ⟨u, hu, hl, rfl, rfl⟩ := h
  exact SheepEven.Step.generic a u hu hl

theorem large_source_generic {A x y : Nat} (h : SheepEven.Step x y)
    (bound : ∀ a u, u%2=1 → x=2^a*u → a≤A) (large : 3*2^A < x) :
    ∃ a, a≤A ∧ Generic a x y := by
  cases h with
  | special a =>
      have ha : a≤A := bound a 3 (by decide) (Nat.mul_comm _ _)
      have hp : 2^a ≤ 2^A := Nat.pow_le_pow_right (by decide) ha
      have hm := Nat.mul_le_mul_left 3 hp
      omega
  | generic a u hu hl =>
      exact ⟨a, bound a u hu rfl, u, hu, hl, rfl, rfl⟩

def cost : List Nat → Nat
  | [] => 0
  | a::as => a+1+cost as

def factor : List Nat → Nat
  | [] => 1
  | a::as => (2^(a+1)+1)*factor as

def Path : List Nat → Nat → Nat → Prop
  | [], x, y => x = y
  | a::as, x, y => ∃ z, Generic a x z ∧ Path as z y

theorem one_affine {a x y : Nat} (h : Generic a x y) :
    2^(a+1)*y + 2^a = (2^(a+1)+1)*x + 2^(a+1)*a := by
  obtain ⟨u, hu, hl, rfl, rfl⟩ := h
  have hh : 2*((u-1)/2)+1=u := by omega
  have hmul : (2^a)*(2*((u-1)/2)+1)=(2^a)*u := congrArg (fun v : Nat => 2^a*v) hh
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have hh' : 2^(a+1)*((u-1)/2)+2^a=2^a*u := by
    simpa [Nat.pow_succ, Nat.mul_assoc] using hmul
  simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul]
  omega

theorem one_difference {a x y x' y' : Nat} (h : Generic a x y)
    (h' : Generic a x' y') :
    2^(a+1)*y + (2^(a+1)+1)*x' = 2^(a+1)*y' + (2^(a+1)+1)*x := by
  have h1 := one_affine h
  have h2 := one_affine h'
  omega

theorem path_difference {w : List Nat} {x y x' y' : Nat} (h : Path w x y)
    (h' : Path w x' y') :
    2^(cost w)*y + factor w*x' = 2^(cost w)*y' + factor w*x := by
  induction w generalizing x y x' y' with
  | nil =>
      dsimp [Path] at h h'
      subst y
      subst y'
      simp [cost, factor,Nat.add_comm]
  | cons a as ih =>
      obtain ⟨z,hz,ht⟩ := h
      obtain ⟨z',hz',ht'⟩ := h'
      have h1 := congrArg (fun n : Nat => factor as*n) (one_difference hz hz')
      have h2 := congrArg (fun n : Nat => 2^(a+1)*n) (ih ht ht')
      simp only [Nat.mul_add] at h1 h2
      have h1' : (2^(a+1)*factor as)*z + ((2^(a+1)+1)*factor as)*x' =
          (2^(a+1)*factor as)*z' + ((2^(a+1)+1)*factor as)*x := by
        simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h1
      have h2' : (2^(a+1)*2^(cost as))*y + (2^(a+1)*factor as)*z' =
          (2^(a+1)*2^(cost as))*y' + (2^(a+1)*factor as)*z := by
        simpa only [Nat.mul_assoc] using h2
      change 2^(a+1+cost as)*y + ((2^(a+1)+1)*factor as)*x' =
        2^(a+1+cost as)*y' + ((2^(a+1)+1)*factor as)*x
      rw [Nat.pow_add]
      omega

theorem factor_odd (w : List Nat) : factor w%2=1 := by
  induction w with
  | nil => decide
  | cons a as ih =>
      have hh : (2^(a+1))%2=0 := by rw [Nat.pow_mod]; simp
      simp only [factor]
      rw [Nat.mul_mod,Nat.add_mod]
      simp [hh,ih]

theorem path_congruence {w : List Nat} {x y x' y' : Nat} (h : Path w x y)
    (h' : Path w x' y') : x % 2^(cost w) = x' % 2^(cost w) := by
  have he := path_difference h h'
  have hc : Nat.Coprime 2 (factor w) := by
    change Nat.gcd 2 (factor w)=1
    rw [Nat.gcd_add_one]
    simp [factor_odd]
  have hc' := hc.pow_left (cost w)
  have hd : 2^(cost w) ∣ factor w*(x-x') := by
    by_cases hh : x'≤x
    · have he' : factor w*(x-x')=2^(cost w)*(y-y') := by
        rw [Nat.mul_sub,Nat.mul_sub]
        omega
      rw [he']
      exact Nat.dvd_mul_right _ _
    · have hh' : x-x'=0 := by omega
      simp [hh']
  have hd' : 2^(cost w) ∣ factor w*(x'-x) := by
    by_cases hh : x≤x'
    · have he' : factor w*(x'-x)=2^(cost w)*(y'-y) := by
        rw [Nat.mul_sub,Nat.mul_sub]
        omega
      rw [he']
      exact Nat.dvd_mul_right _ _
    · have hh' : x'-x=0 := by omega
      simp [hh']
  have hdiv := hc'.dvd_of_dvd_mul_left hd
  have hdiv' := hc'.dvd_of_dvd_mul_left hd'
  by_cases hh : x'≤x
  · obtain ⟨k,hk⟩ := hdiv
    have hx : x=x'+2^(cost w)*k := by omega
    conv => lhs; rw [hx]
    simp [Nat.add_mod]
  · obtain ⟨k,hk⟩ := hdiv'
    have hx : x'=x+2^(cost w)*k := by omega
    conv => rhs; rw [hx]
    simp [Nat.add_mod]

theorem path_injective_below_precision {w : List Nat} {x y x' y' : Nat}
    (h : Path w x y) (h' : Path w x' y')
    (hx : x < 2^(cost w)) (hx' : x' < 2^(cost w)) : x=x' := by
  simpa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx'] using path_congruence h h'

theorem factor_growth (w : List Nat) : 3^w.length ≤ factor w := by
  induction w with
  | nil => decide
  | cons a as ih =>
      have hp : 2^1 ≤ 2^(a+1) := Nat.pow_le_pow_right (by decide) (by omega)
      have hf : 3 ≤ 2^(a+1)+1 := by omega
      have hm := Nat.mul_le_mul hf ih
      simpa only [List.length_cons,Nat.pow_succ,Nat.mul_comm (3^as.length) 3,factor] using hm

#print axioms generic_source
#print axioms large_source_generic
#print axioms one_affine
#print axioms path_difference
#print axioms path_congruence
#print axioms path_injective_below_precision
#print axioms factor_growth
end SheepRawCylinder
