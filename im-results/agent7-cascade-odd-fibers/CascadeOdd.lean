import Std

namespace CascadeOdd

theorem pow_shift18 (n : Nat) : 2 ^ (n + 18) % 9 = 2 ^ n % 9 := by
  rw [Nat.pow_add, Nat.mul_mod]
  have h : 2 ^ 18 % 9 = 1 := by decide
  rw [h]
  simp

theorem pow_mod18 (q r : Nat) : 2 ^ (18 * q + r) % 9 = 2 ^ r % 9 := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      2 ^ (18 * (q + 1) + r) % 9 = 2 ^ ((18 * q + r) + 18) % 9 := by
        have hh : 18 * (q + 1) + r = (18 * q + r) + 18 := by omega
        rw [hh]
      _ = 2 ^ (18 * q + r) % 9 := pow_shift18 _
      _ = 2 ^ r % 9 := ih

theorem exp_dom0 (k : Nat) : 31 * (2 * (k + 10) + 3) ≤ 2 ^ (k + 10) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k+1+10 = k+10+1 by omega, Nat.pow_succ]
    omega

theorem exp_dom (n : Nat) (hn : 10 ≤ n) : 31 * (2*n+3) ≤ 2^n := by
  let k := n - 10
  have hk : n = k + 10 := by dsimp [k]; omega
  rw [hk]
  exact exp_dom0 k

theorem r4 (q : Nat) : 2 ^ (18*q+7) % 9 = ((2*(18*q+4)+3) * 1) % 9 := by
  have hp : 2 ^ (18*q+7) % 9 = 2 ^ 7 % 9 := pow_mod18 q 7
  have hv : 2^7 % 9 = 2 := by decide
  omega

theorem r5 (q : Nat) : 2 ^ (18*q+8) % 9 = ((2*(18*q+5)+3) * 1) % 9 := by
  have hp : 2 ^ (18*q+8) % 9 = 2 ^ 8 % 9 := pow_mod18 q 8
  have hv : 2^8 % 9 = 4 := by decide
  omega

theorem r10 (q : Nat) : 2 ^ (18*q+13) % 9 = ((2*(18*q+10)+3) * 31) % 9 := by
  have hp : 2 ^ (18*q+13) % 9 = 2 ^ 13 % 9 := pow_mod18 q 13
  have hv : 2^13 % 9 = 2 := by decide
  omega

theorem r11 (q : Nat) : 2 ^ (18*q+14) % 9 = ((2*(18*q+11)+3) * 7) % 9 := by
  have hp : 2 ^ (18*q+14) % 9 = 2 ^ 14 % 9 := pow_mod18 q 14
  have hv : 2^14 % 9 = 4 := by decide
  omega

theorem r16 (q : Nat) : 2 ^ (18*q+19) % 9 = ((2*(18*q+16)+3) * 7) % 9 := by
  have hp : 2 ^ (18*q+19) % 9 = 2 ^ 19 % 9 := pow_mod18 q 19
  have hv : 2^19 % 9 = 2 := by decide
  omega

theorem r17 (q : Nat) : 2 ^ (18*q+20) % 9 = ((2*(18*q+17)+3) * 31) % 9 := by
  have hp : 2 ^ (18*q+20) % 9 = 2 ^ 20 % 9 := pow_mod18 q 20
  have hv : 2^20 % 9 = 4 := by decide
  omega

theorem class_exhaustive (n : Nat) (h : n % 6 = 4 ∨ n % 6 = 5) :
    n % 18 = 4 ∨ n % 18 = 5 ∨ n % 18 = 10 ∨
    n % 18 = 11 ∨ n % 18 = 16 ∨ n % 18 = 17 := by
  omega

/-- The even-predecessor chain at a fixed cascade scale. -/
def ancestor (p n j : Nat) : Nat := 8*p + n - 1 - (2*n+3)*2^j

def Q (p n j : Nat) : Nat := 2*ancestor p n j + 5

theorem ancestor_relation (p n j : Nat)
    (hn : 10 ≤ n) (hp : 31*(2*n+3) ≤ 2*p) (hj : j ≤ 4) :
    ancestor p n j + (2*n+3)*2^j = 8*p+n-1 := by
  have hpow : 2^j ≤ 16 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    simpa using this
  have hmul : (2*n+3)*2^j ≤ 16*(2*n+3) := by
    have := Nat.mul_le_mul_left (2*n+3) hpow
    omega
  have hsmall : (2*n+3)*2^j ≤ 8*p+n-1 := by omega
  exact Nat.sub_add_cancel hsmall

theorem ancestor_bounds (p n j : Nat)
    (hn : 10 ≤ n) (hp : 31*(2*n+3) ≤ 2*p) (hj : j ≤ 4) :
    6*p - 1 ≤ ancestor p n j ∧ ancestor p n j ≤ 8*p - 3 := by
  have hr:=ancestor_relation p n j hn hp hj
  have hpow : 2^j ≤ 16 := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) hj
    simpa using this
  have hmul : (2*n+3)*2^j ≤ 16*(2*n+3) := by
    have := Nat.mul_le_mul_left (2*n+3) hpow
    omega
  have hpow1 : 1 ≤ 2^j := Nat.one_le_pow _ _ (by decide)
  have hprodlo : 2*n+3 ≤ (2*n+3)*2^j := by
    have := Nat.mul_le_mul_left (2*n+3) hpow1
    omega
  omega

theorem Q_formula (p n j : Nat)
    (hn : 10 ≤ n) (hp : 31*(2*n+3) ≤ 2*p) (hj : j ≤ 4) :
    Q p n j + (2*n+3)*(2^(j+1)-1) = 16*p := by
  have hr:=ancestor_relation p n j hn hp hj
  have hone : 1 ≤ 2^(j+1) := Nat.one_le_pow _ _ (by decide)
  have hmul :
      (2*n+3)*(2^(j+1)-1) + (2*n+3) = 2*((2*n+3)*2^j) := by
    calc
      (2*n+3)*(2^(j+1)-1) + (2*n+3) =
          (2*n+3)*((2^(j+1)-1)+1) := by simp [Nat.mul_add]
      _ = (2*n+3)*2^(j+1) := by rw [Nat.sub_add_cancel hone]
      _ = 2*((2*n+3)*2^j) := by
        rw [Nat.pow_succ]
        simp only [Nat.mul_comm, Nat.mul_assoc]
  dsimp [Q]
  omega

theorem Q_bounds (p n j : Nat)
    (hn : 10 ≤ n) (hp : 31*(2*n+3) ≤ 2*p) (hj : j ≤ 4) :
    14*p ≤ Q p n j ∧ Q p n j ≤ 16*p := by
  have hf:=Q_formula p n j hn hp hj
  have hpow : 2^(j+1) ≤ 32 := by
    have : j+1 ≤ 5 := by omega
    have := Nat.pow_le_pow_right (by decide : 0 < 2) this
    simpa using this
  have hlow : 1 ≤ 2^(j+1) := Nat.one_le_pow _ _ (by decide)
  have hmul : (2*n+3)*(2^(j+1)-1) ≤ 31*(2*n+3) := by
    have := Nat.mul_le_mul_left (2*n+3) (show 2^(j+1)-1 ≤ 31 by omega)
    omega
  omega

theorem pow_as_p (n : Nat) (hn : 1 ≤ n) :
    16 * 2^(n-1) = 2^(n+3) := by
  have he : n+3 = (n-1)+4 := by omega
  rw [he, Nat.pow_add]
  simp [show 2^4 = 16 by decide, Nat.mul_comm]

/-- Unified modular obstruction under the two surviving fatal-height classes. -/
theorem mod_open (n : Nat) (h : n % 6 = 4 ∨ n % 6 = 5) :
    ∃ j : Nat, (j = 0 ∨ j = 2 ∨ j = 4) ∧
      2^(n+3) % 9 = ((2*n+3)*(2^(j+1)-1)) % 9 := by
  have hc := class_exhaustive n h
  rcases hc with h4 | h5 | h10 | h11 | h16 | h17
  · refine ⟨0, Or.inl rfl, ?_⟩
    have he : n = 18*(n/18)+4 := by omega
    rw [he]
    simpa [show 18*(n/18)+4+3 = 18*(n/18)+7 by omega] using r4 (n/18)
  · refine ⟨0, Or.inl rfl, ?_⟩
    have he : n = 18*(n/18)+5 := by omega
    rw [he]
    simpa [show 18*(n/18)+5+3 = 18*(n/18)+8 by omega] using r5 (n/18)
  · refine ⟨4, Or.inr (Or.inr rfl), ?_⟩
    have he : n = 18*(n/18)+10 := by omega
    rw [he]
    simpa [show 18*(n/18)+10+3 = 18*(n/18)+13 by omega] using r10 (n/18)
  · refine ⟨2, Or.inr (Or.inl rfl), ?_⟩
    have he : n = 18*(n/18)+11 := by omega
    rw [he]
    simpa [show 18*(n/18)+11+3 = 18*(n/18)+14 by omega] using r11 (n/18)
  · refine ⟨2, Or.inr (Or.inl rfl), ?_⟩
    have he : n = 18*(n/18)+16 := by omega
    rw [he]
    simpa [show 18*(n/18)+16+3 = 18*(n/18)+19 by omega] using r16 (n/18)
  · refine ⟨4, Or.inr (Or.inr rfl), ?_⟩
    have he : n = 18*(n/18)+17 := by omega
    rw [he]
    simpa [show 18*(n/18)+17+3 = 18*(n/18)+20 by omega] using r17 (n/18)

theorem p_bound (n : Nat) (hn : 10 ≤ n) :
    31*(2*n+3) ≤ 2*2^(n-1) := by
  have hb:=exp_dom n hn
  have he : n = (n-1)+1 := by omega
  rw [he, Nat.pow_succ] at hb
  omega

theorem Q_mod9_zero (n j : Nat) (hn : 10 ≤ n) (hj : j ≤ 4)
    (hmod : 2^(n+3)%9 = ((2*n+3)*(2^(j+1)-1))%9) :
    Q (2^(n-1)) n j % 9 = 0 := by
  have hp:=p_bound n hn
  have hf:=Q_formula (2^(n-1)) n j hn hp hj
  have hpow:=pow_as_p n (by omega)
  omega

/-- Exactly the scale interval and 3-adic k=1 algebra needed for an odd-exit ancestor. -/
theorem odd_gate (p n j : Nat) (hn : 10 ≤ n)
    (hp : 31*(2*n+3) ≤ 2*p) (hj : j ≤ 4)
    (hd : Q p n j % 9 = 0) :
    ∃ (a h : Nat),
      3*p-2 ≤ a ∧ a ≤ 4*p-4 ∧
      h+4*p+n = 2*a+3 ∧
      a+3 = 2*(Q p n j/9) ∧
      (Q p n j/9)%2=1 ∧
      (9*((a+3)/2)-5)/2 = ancestor p n j := by
  let q := Q p n j / 9
  have hq : 9*q = Q p n j := by
    have ht:=Nat.mod_add_div (Q p n j) 9
    dsimp [q]
    omega
  have hQt : Q p n j = 2*ancestor p n j+5 := rfl
  have hodd : q % 2 = 1 := by omega
  have hb:=Q_bounds p n j hn hp hj
  have hp9 : 9 ≤ p := by omega
  let a := 2*q-3
  have haeq : a+3=2*q := by dsimp [a]; omega
  have hlo : 3*p-2 ≤ a := by dsimp [a]; omega
  have hhi : a ≤ 4*p-4 := by dsimp [a]; omega
  have hnsmall : n+1 ≤2*p := by omega
  have hnonneg : 4*p+n ≤2*a+3 := by omega
  let h := 2*a-4*p-n+3
  have hheq : h+4*p+n=2*a+3 := by dsimp [h]; omega
  have hhal : (a+3)/2=q := by omega
  have hout : (9*((a+3)/2)-5)/2=ancestor p n j := by
    rw [hhal]
    omega
  exact ⟨a,h,hlo,hhi,hheq,haeq,hodd,hout⟩

/-- The unique legal even-exit inverse at the same cascade scale. -/
theorem even_chain (p n j : Nat) (hn : 10 ≤ n)
    (hp : 31*(2*n+3) ≤ 2*p) (hj : j < 4) :
    6*p-1 ≤ ancestor p n j ∧ ancestor p n j ≤ 8*p-3 ∧
    ancestor p n (j+1) + 8*p + n - 1 = 2*ancestor p n j := by
  have hj0 : j ≤ 4 := by omega
  have hj1 : j+1 ≤4 := by omega
  have hbound:=ancestor_bounds p n j hn hp hj0
  have hr:=ancestor_relation p n j hn hp hj0
  have hr1:=ancestor_relation p n (j+1) hn hp hj1
  have hpow : (2*n+3)*2^(j+1) = 2*((2*n+3)*2^j) := by
    rw [Nat.pow_succ]
    simp only [Nat.mul_comm, Nat.mul_assoc]
  constructor
  · exact hbound.1
  constructor
  · exact hbound.2
  · omega

/-- All six unresolved index classes have a k=1 odd-exit ancestor after at most four even inversions. -/
theorem open_has_odd (n : Nat) (hn : 10 ≤ n)
    (hc : n%6=4 ∨ n%6=5) :
    ∃ (j a h : Nat), (j=0 ∨ j=2 ∨ j=4) ∧
      3*2^(n-1)-2 ≤ a ∧ a ≤ 4*2^(n-1)-4 ∧
      h+4*2^(n-1)+n=2*a+3 ∧
      a+3=2*(Q (2^(n-1)) n j/9) ∧
      (Q (2^(n-1)) n j/9)%2=1 ∧
      (9*((a+3)/2)-5)/2=ancestor (2^(n-1)) n j ∧
      (∀ i : Nat, i<j →
        6*2^(n-1)-1 ≤ ancestor (2^(n-1)) n i ∧
        ancestor (2^(n-1)) n i ≤ 8*2^(n-1)-3 ∧
        ancestor (2^(n-1)) n (i+1)+8*2^(n-1)+n-1 =
          2*ancestor (2^(n-1)) n i) := by
  obtain ⟨j, hj, hmod⟩ := mod_open n hc
  have hj4 : j≤4 := by rcases hj with h0|h2|h4 <;> omega
  have hp:=p_bound n hn
  have hd:=Q_mod9_zero n j hn hj4 hmod
  obtain ⟨a,h, hlo,hhi,hheq,haeq, hodd,hout⟩ :=
    odd_gate (2^(n-1)) n j hn hp hj4 hd
  refine ⟨j,a,h,hj,hlo,hhi,hheq,haeq,hodd,hout,?_⟩
  intro i hi
  have he:=even_chain (2^(n-1)) n i hn hp (by omega)
  exact he

/-- Uniform witness proposition, including the two finite exceptional indices. -/
def Certificate (n j a h : Nat) : Prop :=
  (j=0 ∨ j=2 ∨ j=4) ∧
    3*2^(n-1)-2 ≤ a ∧ a ≤ 4*2^(n-1)-4 ∧
    h+4*2^(n-1)+n=2*a+3 ∧
    a+3=2*(Q (2^(n-1)) n j/9) ∧
    (Q (2^(n-1)) n j/9)%2=1 ∧
    (9*((a+3)/2)-5)/2=ancestor (2^(n-1)) n j ∧
    (∀ i : Nat, i<j →
      6*2^(n-1)-1 ≤ ancestor (2^(n-1)) n i ∧
      ancestor (2^(n-1)) n i ≤ 8*2^(n-1)-3 ∧
      ancestor (2^(n-1)) n (i+1)+8*2^(n-1)+n-1 =
        2*ancestor (2^(n-1)) n i)

theorem all_surviving_have_odd_parent (n : Nat) (hn : 4≤n)
    (hc : n%6=4 ∨ n%6=5) :
    ∃ (j a h : Nat), Certificate n j a h := by
  by_cases h10 : 10≤n
  · simpa only [Certificate] using open_has_odd n h10 hc
  · have hh : n=4 ∨ n=5 := by omega
    rcases hh with rfl | rfl
    · refine ⟨0,23,13,?_⟩
      simp [Certificate, ancestor, Q]
    · refine ⟨0,51,36,?_⟩
      simp [Certificate, ancestor, Q]

#print axioms all_surviving_have_odd_parent

end CascadeOdd
