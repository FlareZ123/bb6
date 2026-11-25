import Std

namespace F119Inverse2

-- The signed power residue lemma is adapted from F119.power_residue,
-- im-results/agent40-f119-ternary/F119.lean.
theorem signed_residue (h k : Nat) (hh : 1 ≤ h) :
    ∃ j, j ≤ h ∧ (3^k % (3*3^h+1)=3^j ∨ 3^k % (3*3^h+1)=3*3^h+1-3^j) := by
  let M := 3*3^h+1
  have hp : 3 ≤ 3^h := Nat.pow_le_pow_right (n:=3) (by decide) hh
  have hM : 3<M := by dsimp [M]; omega
  induction k with
  | zero => exact ⟨0,by omega,Or.inl (Nat.mod_eq_of_lt (by dsimp [M]; omega))⟩
  | succ k ih =>
    obtain ⟨j,hj,hr⟩ := ih
    have hq : 3^j ≤ 3^h := Nat.pow_le_pow_right (n:=3) (by decide) hj
    have hqpos : 0 < 3^j := Nat.pow_pos (by decide)
    have hnext : 3^(k+1)%M = (3*(3^k%M))%M := by
      rw [Nat.pow_succ, Nat.mul_comm (3^k) 3, Nat.mul_mod, Nat.mod_eq_of_lt hM]
    change 3^k % M = 3^j ∨ 3^k % M = M-3^j at hr
    change ∃ j, j ≤ h ∧ (3^(k+1)%M=3^j ∨ 3^(k+1)%M=M-3^j)
    rw [hnext]
    rcases hr with hr|hr
    · rw [hr, Nat.mod_eq_of_lt (by dsimp [M]; omega)]
      by_cases he : j=h
      · subst j
        exact ⟨0,by omega,Or.inr (by simp [M])⟩
      · exact ⟨j+1,by omega,Or.inl (by rw [Nat.pow_succ, Nat.mul_comm])⟩
    · rw [hr]
      have heq : 3*(M-3^j)=M*2+(M-3*3^j) := by dsimp [M]; omega
      rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt (by dsimp [M]; omega)]
      by_cases he : j=h
      · subst j
        exact ⟨0,by omega,Or.inl (by dsimp [M]; simp)⟩
      · exact ⟨j+1,by omega,Or.inr (by rw [Nat.pow_succ,Nat.mul_comm])⟩

theorem large_gap (h : Nat) (hh : 6 ≤ h) : 2*(39+10*(h+4)) < 3^h := by
  induction h with
  | zero => omega
  | succ h ih =>
    by_cases hb : 6 ≤ h
    · have h1 := ih hb
      rw [Nat.pow_succ]
      omega
    · have he : h=5 := by omega
      subst h
      decide

-- Exact affine equation for the generic predecessor of a first inverse node.
def rhs (C h r t : Nat) : Nat :=
  10*((3*3^h+1)*t + 3^h*r + h+3 + (if r=2 then 1 else 0)) + C

theorem high_excluded (C h r t k : Nat) (hc : C=33 ∨ C=39)
    (hh : 6 ≤ h) (hr : r=1 ∨ r=2) : rhs C h r t ≠ 3^(k+2) := by
  intro eq
  let p := 3^h
  let M := 3*p+1
  have hg := large_gap h hh
  have hp : 729 ≤ p := Nat.pow_le_pow_right (n:=3) (by decide) hh
  change 2*(39+10*(h+4)) < p at hg
  obtain ⟨j,hj,hs⟩ := signed_residue h (k+2) (by omega)
  have hjp : 3^j ≤ p := Nat.pow_le_pow_right (n:=3) (by decide) hj
  change 3^(k+2)%M=3^j ∨ 3^(k+2)%M=M-3^j at hs
  have hmul : M*(10*t) = 10*(M*t) := by rw [← Nat.mul_assoc, Nat.mul_comm M 10, Nat.mul_assoc]
  rcases hr with rfl|rfl
  · have he : 3^(k+2) = M*(10*t+3)+(p+10*(h+3)+C-3) := by
      rw [← eq]
      unfold rhs
      simp only [Nat.reduceEqDiff, ite_false, Nat.mul_add, Nat.mul_one, Nat.add_zero]
      rw [hmul]
      dsimp [M,p]
      omega
    have hmod : 3^(k+2)%M=p+10*(h+3)+C-3 := by
      rw [he,Nat.mul_add_mod,Nat.mod_eq_of_lt (by dsimp [M]; omega)]
    rw [hmod] at hs
    dsimp [M] at hs
    omega
  · have he : 3^(k+2) = M*(10*t+6)+(2*p+10*(h+4)+C-6) := by
      rw [← eq]
      unfold rhs
      simp only [ite_true, Nat.mul_add]
      rw [hmul]
      dsimp [M,p]
      omega
    have hmod : 3^(k+2)%M=2*p+10*(h+4)+C-6 := by
      rw [he,Nat.mul_add_mod,Nat.mod_eq_of_lt (by dsimp [M]; omega)]
    rw [hmod] at hs
    have hjlt : j<h := by
      apply Nat.lt_of_not_ge
      intro hno
      have heq : j=h := by omega
      subst j
      change 2*p+10*(h+4)+C-6=p ∨ 2*p+10*(h+4)+C-6=M-p at hs
      dsimp [M] at hs
      omega
    have hjp' : 3^j ≤ 3^(h-1) := Nat.pow_le_pow_right (n:=3) (by decide) (show j≤h-1 by omega)
    have hpi : p=3*3^(h-1) := by
      have he : h=(h-1)+1 := by omega
      calc
        p = 3^h := rfl
        _ = 3^((h-1)+1) := congrArg (3^·) he
        _ = 3*3^(h-1) := by rw [Nat.pow_succ,Nat.mul_comm]
    dsimp [M] at hs
    omega


def modulus (h : Nat) := 10*(3*3^h+1)
def offset (C h r : Nat) := 10*(3^h*r+h+3+(if r=2 then 1 else 0))+C

theorem congruence (C h r t k : Nat) (he : rhs C h r t = 3^(k+2)) :
    3^(k+2) % modulus h = offset C h r % modulus h := by
  have e : rhs C h r t = modulus h*t+offset C h r := by
    unfold rhs modulus offset
    rw [Nat.mul_assoc 10 (3*3^h+1) t]
    simp only [Nat.mul_add]
    omega
  rw [← he,e,Nat.mul_add_mod]

theorem periodic (m k : Nat) (hm : 1<m) (hp : 3^120 % m=1) :
    3^(k+2)%m=3^(k%120+2)%m := by
  have he : k+2=120*(k/120)+(k%120+2) := by omega
  conv => lhs; rw [he,Nat.pow_add,Nat.pow_mul,Nat.mul_mod]
  rw [Nat.pow_mod,hp, Nat.one_pow, Nat.mod_eq_of_lt hm, Nat.one_mul, Nat.mod_mod]

-- The finite check covers a complete period, including h=0 and both branches.
theorem finite_rows : ∀ (h : Fin 6) (k : Fin 120) (r : Fin 2),
    (3^(k.val+2)%modulus h.val = offset 39 h.val (r.val+1)%modulus h.val ∧ k.val%12=0 →
      h.val=1 ∧ ((r.val=0 ∧ k.val%60=0) ∨ (r.val=1 ∧ k.val%60=48))) ∧
    (3^(k.val+2)%modulus h.val = offset 33 h.val (r.val+1)%modulus h.val ∧ k.val%12=3 →
      h.val=1 ∧ ((r.val=0 ∧ k.val%60=39) ∨ (r.val=1 ∧ k.val%60=3))) := by
  decide

theorem finite_period : ∀ h : Fin 6, 3^120 % modulus h.val=1 ∧ 1<modulus h.val := by decide

theorem second_gate (C h r t k : Nat)
    (hc : (C=39 ∧ k%12=0) ∨ (C=33 ∧ k%12=3)) (hr : r=1 ∨ r=2)
    (he : rhs C h r t=3^(k+2)) :
    h=1 ∧ ((C=39 ∧ ((r=1 ∧ k%60=0) ∨ (r=2 ∧ k%60=48))) ∨
           (C=33 ∧ ((r=1 ∧ k%60=39) ∨ (r=2 ∧ k%60=3)))) := by
  have hlt : h<6 := by
    apply Nat.lt_of_not_ge
    intro hh
    exact high_excluded C h r t k (by omega) hh hr he
  let hf : Fin 6 := ⟨h,hlt⟩
  let kf : Fin 120 := ⟨k%120,Nat.mod_lt _ (by decide)⟩
  let rf : Fin 2 := ⟨r-1,by omega⟩
  have hp := finite_period hf
  have hcng := congruence C h r t k he
  rw [periodic (modulus h) k hp.2 hp.1] at hcng
  have H := finite_rows hf kf rf
  dsimp [hf,kf,rf] at H
  have h12 : k%120%12=k%12 := by omega
  have h60 : k%120%60=k%60 := by omega
  have hr' : r-1+1=r := by omega
  rw [h12,h60,hr'] at H
  rcases hc with ⟨rfl,hk⟩|⟨rfl,hk⟩
  · have h0 := H.1 ⟨hcng,hk⟩
    omega
  · have h0 := H.2 ⟨hcng,hk⟩
    omega

#print axioms second_gate

-- The exceptional tag-2 and pure-power sources cannot feed either first
-- inverse family once k >= 4. These bounds use only the root invariant.
theorem linear_pow (a : Nat) : a+1 ≤ 3^a := by
  induction a with
  | zero => decide
  | succ a ih => rw [Nat.pow_succ]; omega

theorem small_linear (b : Nat) (hb : 3≤b) : 7*b+19 < 2*3^b := by
  induction b with
  | zero => omega
  | succ b ih =>
    by_cases h : 3≤b
    · have h1 := ih h
      rw [Nat.pow_succ]
      omega
    · have he : b=2 := by omega
      subst b
      decide

theorem target_window (C k y : Nat) (hc : C=33 ∨ C=39) (hk : 4≤k)
    (hy : 10*y+C=3^(k+2)) : 2*3^(k-1)<y ∧ y<3^k := by
  have e : 3^(k+2)=9*3^k := by rw [Nat.pow_add]; omega
  have e' : 3^k=3*3^(k-1) := by
    conv => lhs; rw [show k=k-1+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have hq : 27≤3^(k-1) := Nat.pow_le_pow_right (n:=3) (by decide) (show 3≤k-1 by omega)
  omega

theorem exponent_lt (a k y : Nat) (ha : 3^a<y) (hy : y<3^k) : a<k := by
  apply Nat.lt_of_not_ge
  intro h
  have hh := Nat.pow_le_pow_right (n:=3) (by decide) h
  omega

theorem no_power_parent (C k y a : Nat) (hc : C=33 ∨ C=39) (hk : 4≤k)
    (hy : 10*y+C=3^(k+2)) (he : y=3^a+a+3) : False := by
  have hw := target_window C k y hc hk hy
  have ha := exponent_lt a k y (by omega) hw.2
  have hp := Nat.pow_le_pow_right (n:=3) (by decide) (show a≤k-1 by omega)
  have hl := small_linear (k-1) (by omega)
  omega

theorem no_tag_two_parent (C k y a h t r : Nat) (hc : C=33 ∨ C=39) (hk : 4≤k)
    (ha : 2≤a) (hr : r=1 ∨ r=2)
    (hx : 3^a+a+1=3^h*(3*t+r)) (hy : 10*y+C=3^(k+2))
    (he : y=3^a+a+1+2+h+t+r+1) : False := by
  have hw := target_window C k y hc hk hy
  have hak := exponent_lt a k y (by omega) hw.2
  have hpa := Nat.pow_le_pow_right (n:=3) (by decide) (show a≤k-1 by omega)
  have hm : 0<3*t+r := by omega
  have hp : 3^h≤3^a+a+1 := by rw [hx]; exact Nat.le_mul_of_pos_right _ hm
  have hbound : 3^a+a+1<3^(a+1) := by
    have hl := linear_pow a
    have hpos : 0<3^a := Nat.pow_pos (by decide)
    rw [Nat.pow_succ]
    omega
  have hha : h≤a := by
    apply Nat.le_of_not_gt
    intro hgt
    have hh := Nat.pow_le_pow_right (n:=3) (by decide) (show a+1≤h by omega)
    omega
  have ht : 3*t+r≤3^a+a+1 := by rw [hx]; exact Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
  have hl := small_linear (k-1) (by omega)
  omega

#print axioms no_power_parent
#print axioms no_tag_two_parent
end F119Inverse2
