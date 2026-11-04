import Std

namespace Agent22Special

theorem mul_neg_one_mod (m t : Nat) (_hm : 1 < m)
    (ht0 : 0 < t) (ht : t < m) : ((m-1)*t)%m = m-t := by
  have hmt : m ≤ m*t := by
    have h := Nat.mul_le_mul_left m (show 1 ≤ t by omega)
    simpa using h
  have hmul : (m-1)*t = m*(t-1)+(m-t) := by
    rw [Nat.sub_mul, Nat.mul_sub_left_distrib]
    simp only [Nat.one_mul, Nat.mul_one]
    omega
  rw [hmul, Nat.add_mod, Nat.mul_mod_right]
  simp [Nat.mod_eq_of_lt (by omega : m - t < m)]

theorem double_lin_bound (n : Nat) : 2*(n+4) ≤ 2^(n+3) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have hpow : 2 ≤ (2:Nat)^(n+3) := by
      calc
        2 = 2^1 := by decide
        _ ≤ 2^(n+3) := Nat.pow_le_pow_right (by decide) (by omega)
    have hexp : (2:Nat)^(n.succ+3)=2^(n+3)*2 := by
      rw [show n.succ+3 = (n+3)+1 by omega, Nat.pow_succ]
    rw [hexp]
    omega

theorem mod_target_odd (b : Nat) (hb : 5 ≤ b) : (2*b-1)%2=1 := by
  omega

theorem even_triple_pow (r : Nat) (hr : 1 ≤ r) : (3*2^r)%2=0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod]
  simp

theorem pow_b_relation (b : Nat) (hb : 1 ≤ b) : (2:Nat)^(b+1) = 4*2^(b-1) := by
  have h : b+1=(b-1)+2 := by omega
  rw [h, Nat.pow_add]
  simp [Nat.mul_comm]

theorem small_triple_lt (b r : Nat) (hb : 5 ≤ b) (hr : r < b) :
    3*2^r < (2:Nat)^(b+1)+1 := by
  have hpow : (2:Nat)^r ≤ 2^(b-1) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_b_relation b (by omega)]
  omega

theorem small_triple_mod (b r : Nat) (hb : 5 ≤ b) (hr : r < b) :
    (3*2^r)%((2:Nat)^(b+1)+1) = 3*2^r := by
  exact Nat.mod_eq_of_lt (small_triple_lt b r hb hr)

theorem middle_triple_mod (b : Nat) (_hb : 5 ≤ b) :
    (3*2^b)%((2:Nat)^(b+1)+1) = 2^b-1 := by
  have hpow : (2:Nat)^(b+1) = 2^b*2 := by rw [Nat.pow_succ]
  have hp : 0 < (2:Nat)^b := Nat.two_pow_pos b
  have heq : 3*2^b = ((2:Nat)^(b+1)+1)+(2^b-1) := by
    rw [hpow]; omega
  rw [heq, Nat.add_mod_left]
  exact Nat.mod_eq_of_lt (by rw [hpow]; omega)

theorem lin_pow_b (b : Nat) (hb : 4 ≤ b) : 2*b ≤ 2^(b-1) := by
  have h := double_lin_bound (b-4)
  have h1 : b-4+4=b := by omega
  have h2 : b-4+3=b-1 := by omega
  rw [h1,h2] at h
  exact h

theorem small_residue_gap (b r : Nat) (hb : 5 ≤ b) (hr : r ≤ b) :
  let m := (2:Nat)^(b+1)+1
  let k := 2*b-1
  let t := (3*2^r)%m
  0<t ∧ t≠k ∧ m-t≠k := by
  dsimp
  have hlin := lin_pow_b b (by omega)
  have hpow : 0<(2:Nat)^r := Nat.two_pow_pos r
  by_cases hreq : r=b
  · subst r
    rw [middle_triple_mod b hb]
    have htwo : (2:Nat)^b = 2*2^(b-1) := by
      calc
        (2:Nat)^b = 2^((b-1)+1) := by congr 1; omega
        _ = 2^(b-1)*2 := Nat.pow_succ 2 (b-1)
        _ = 2*2^(b-1) := by rw [Nat.mul_comm]
    rw [htwo]
    have hmiddle : 0 < (2:Nat)^(b-1) := Nat.two_pow_pos (b-1)
    have htwop : (2:Nat)^(b+1) = 4*2^(b-1) := pow_b_relation b (by omega)
    rw [htwop]
    omega
  · have hrl : r<b := by omega
    rw [small_triple_mod b r hb hrl]
    have hsmall : 3*2^r < (2:Nat)^(b+1)+1 := small_triple_lt b r hb hrl
    have hpowr : (2:Nat)^r ≤ 2^(b-1) := Nat.pow_le_pow_right (by decide) (by omega)
    have htwop : (2:Nat)^(b+1) = 4*2^(b-1) := pow_b_relation b (by omega)
    rw [htwop] at *
    by_cases hr0 : r = 0
    · subst r
      simp only [Nat.pow_zero, Nat.mul_one] at *
      omega
    · have hEven := even_triple_pow r (by omega)
      have hOdd := mod_target_odd b hb
      omega

theorem triple_flip (b n : Nat) (_hb : 5 ≤ b)
    (ht : 0 < (3*2^n)%((2:Nat)^(b+1)+1)) :
    (3*2^(n+b+1))%((2:Nat)^(b+1)+1) =
    ((2:Nat)^(b+1)+1) - (3*2^n)%((2:Nat)^(b+1)+1) := by
  let m := (2:Nat)^(b+1)+1
  have hm : 1 < m := by
    dsimp [m]
    have h := Nat.two_pow_pos (b+1)
    omega
  have hpow : (2:Nat)^(b+1)%m = m-1 := by
    dsimp [m]
    have h := Nat.two_pow_pos (b+1)
    rw [Nat.mod_eq_of_lt (by omega)]
  have hlt : (3*2^n)%m < m := Nat.mod_lt _ (by omega)
  rw [show n+b+1=n+(b+1) by omega, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_mod, hpow]
  rw [Nat.mul_comm ((3*2^n)%m)]
  exact mul_neg_one_mod m ((3*2^n)%m) hm ht hlt

theorem triple_period (b n : Nat) (hb : 5 ≤ b)
    (ht : 0 < (3*2^n)%((2:Nat)^(b+1)+1)) :
    (3*2^(n+2*(b+1)))%((2:Nat)^(b+1)+1) =
    (3*2^n)%((2:Nat)^(b+1)+1) := by
  let m := (2:Nat)^(b+1)+1
  have hm : 0 < m := by
    dsimp [m]
    have hp := Nat.two_pow_pos (b+1)
    omega
  have h1 : (3*2^(n+b+1))%m = m-(3*2^n)%m := triple_flip b n hb ht
  have hlt : (3*2^n)%m < m := Nat.mod_lt _ hm
  have hpos : 0 < (3*2^(n+b+1))%m := by
    rw [h1]
    omega
  have h2 : (3*2^((n+b+1)+b+1))%m = m-(3*2^(n+b+1))%m :=
    triple_flip b (n+b+1) hb hpos
  have hexp : n+2*(b+1) = (n+b+1)+b+1 := by omega
  rw [hexp, h2, h1]
  exact Nat.sub_sub_self (Nat.le_of_lt hlt)

theorem full_residue_gap (b n : Nat) (hb : 5 ≤ b) :
  let m := (2:Nat)^(b+1)+1
  let k := 2*b-1
  let t := (3*2^n)%m
  0<t ∧ t≠k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    dsimp
    by_cases hn : n < 2*(b+1)
    · by_cases hnlow : n ≤ b
      · have h := small_residue_gap b n hb hnlow
        exact ⟨h.1,h.2.1⟩
      · let r := n-(b+1)
        have hr : r ≤ b := by dsimp [r]; omega
        have hsmall := small_residue_gap b r hb hr
        have htr := triple_flip b r hb hsmall.1
        have hexp : n=r+b+1 := by dsimp [r]; omega
        rw [hexp, htr]
        have hlt : (3*2^r)%((2:Nat)^(b+1)+1) < (2:Nat)^(b+1)+1 :=
          Nat.mod_lt _ (by have hh := Nat.two_pow_pos (b+1); omega)
        exact ⟨by omega, hsmall.2.2⟩
    · let r := n-2*(b+1)
      have hr : r<n := by dsimp [r]; omega
      have hprev := ih r hr
      have heq : n = r+2*(b+1) := by dsimp [r]; omega
      rw [heq, triple_period b r hb hprev.1]
      exact hprev

#print axioms full_residue_gap

/-- A coefficient-three, all-exponent obstruction for *every* high generic
    Sheep source valuation. The full exponent and the cofactor are unbounded. -/
theorem no_generic_high (a b v : Nat) (hb : 5 ≤ b) :
    ((2:Nat)^(b+1)+1)*v+2*b ≠ 3*2^(a+1)+1 := by
  intro heq
  let m := (2:Nat)^(b+1)+1
  let k := 2*b-1
  have hlin := lin_pow_b b (by omega)
  have hpowrel := pow_b_relation b (by omega)
  have hpos : 0 < (2:Nat)^(b-1) := Nat.two_pow_pos (b-1)
  have hk : k<m := by
    dsimp [k,m]
    rw [hpowrel]
    omega
  have heq' : 3*2^(a+1) = m*v+k := by
    dsimp [m,k] at *
    omega
  have hmod : (3*2^(a+1))%m = k := by
    rw [heq', Nat.add_mod, Nat.mul_mod_right]
    simp [Nat.mod_eq_of_lt hk]
  have hgap := (full_residue_gap b (a+1) hb).2
  exact hgap hmod

#print axioms no_generic_high

end Agent22Special
