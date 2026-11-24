import Std

namespace BB6.Agent32F418.Arithmetic

/-- A gap has an odd part greater than one: it cannot be a power of two. -/
def NonPower (n : Nat) : Prop := ∃ e q : Nat, 0 < q ∧ n = 2^e * (2*q+1)

theorem nonPower_not_pow {n : Nat} (h : NonPower n) (j : Nat) : n ≠ 2^j := by
  obtain ⟨e,q,hq,he⟩ := h
  intro hj
  have he' : 2^e ∣ 2^j := ⟨2*q+1, by omega⟩
  have hle : e ≤ j := (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < 2)).mp he'
  obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le hle
  subst j
  rw [Nat.pow_add] at hj
  have hp : 0 < 2^e := Nat.two_pow_pos _
  have hq' : 2*q+1 = 2^d := by
    apply Nat.eq_of_mul_eq_mul_left hp
    omega
  cases d with
  | zero => simp at hq'; omega
  | succ d => rw [Nat.pow_succ] at hq'; omega

theorem factor_nonzero_tail {N j Q : Nat} (h : NonPower N)
    (hf : N = 2^j * (2*Q+1)) : Q > 0 := by
  by_cases hz : Q = 0
  · simp [hz] at hf
    exact False.elim (nonPower_not_pow h j hf)
  · omega

/-- `w` is the exponent of the upper power-of-two boundary, not log2 n. -/
def RightWidth (n w : Nat) : Prop := 0 < w ∧ 2^(w-1) ≤ n ∧ n < 2^w

def gap (n w : Nat) := 2^w - n

theorem gap_pos {n w : Nat} (h : RightWidth n w) : 0 < gap n w := by
  unfold gap; exact Nat.sub_pos_of_lt h.2.2

theorem pow_bound_twice {w : Nat} (hw : 0 < w) : 2^w = 2*2^(w-1) := by
  have h : 2^((w-1)+1) = 2*2^(w-1) := by rw [Nat.pow_succ,Nat.mul_comm]
  rwa [show w-1+1 = w by omega] at h

theorem standard_zero_overflow {N n w : Nat} (hw : RightWidth n w) (hN : N < n) :
    let t := gap n w
    0 < N+t ∧ N+t < 2^w ∧ RightWidth (2^w) (w+1) ∧
      N+t < gap (2^w) (w+1) := by
  have hp := gap_pos hw
  have hlt := hw.2.2
  unfold gap at hp
  simp only [gap, RightWidth, Nat.add_sub_cancel, Nat.pow_succ]
  omega

theorem standard_one_overflow {n w : Nat} (hw : RightWidth n w)
    (hn : NonPower (gap n w)) :
    let t := gap n w
    0 < t ∧ t < 2^(w-1) ∧ RightWidth (2^(w-1)) w ∧
      gap (2^(w-1)) w = 2^(w-1) ∧ NonPower t := by
  have hp := gap_pos hw
  have hb := pow_bound_twice hw.1
  have hne := nonPower_not_pow hn (w-1)
  simp only [gap, RightWidth] at *
  refine ⟨by omega, by omega, ⟨hw.1, by omega, by omega⟩, by omega, hn⟩

/-- The pre-collision left increments for alignment 1 or 2 fit strictly
    before the next right overflow, even at arbitrary width. -/
theorem shifted12_budget {N j Q t : Nat} (hf : N = 2^j * (2*Q+1))
    (ht : N < t) :
    let z := 2^j-1
    z < t ∧ Q + 2 ≤ t-z := by
  have hp := Nat.two_pow_pos j
  have hm : 2*Q+1 ≤ 2^j*(2*Q+1) := by
    simpa using Nat.mul_le_mul_right (2*Q+1) hp
  have hq : Q ≤ 2^j*Q := by simpa using Nat.mul_le_mul_right Q hp
  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, Nat.mul_comm (2^j) 2, Nat.mul_assoc] at hf
  omega

/-- Alignment 4 is entered with a power-of-two right gap. Its extra
    lower-counter pass still cannot hit right overflow before collision. -/
theorem shifted4_budget {N j Q W : Nat} (hf : N = 2^j * (2*Q+1))
    (ht : N < 2^W) :
    let z := 2^(j+1)-1
    z < 2^W ∧ Q+1 ≤ 2^W-z := by
  have hp := Nat.two_pow_pos j
  have hbase : 2^j ≤ N := by
    rw [hf]; simpa using Nat.mul_le_mul_left (2^j) (show 1 ≤ 2*Q+1 by omega)
  have hlt : j < W := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega : 2^j < 2^W)
  have hdiv : 2^(j+1) ∣ 2^W := Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨k,hk⟩ := hdiv
  have hj : 2^(j+1) = 2*2^j := by rw [Nat.pow_succ, Nat.mul_comm]
  have hQ : Q < k := by
    have hmul : 2^j*(2*Q+1) < 2^j*(2*k) := by
      calc
        _ = N := hf.symm
        _ < 2^W := ht
        _ = 2^j*(2*k) := by rw [hk,hj]; ac_rfl
    exact (by have h := (Nat.mul_lt_mul_left hp).mp hmul; omega)
  have hprod : Q ≤ 2^(j+1)*(k-1) := by
    have hpos := Nat.two_pow_pos (j+1)
    have h1 : k-1 ≤ 2^(j+1)*(k-1) := by simpa using Nat.mul_le_mul_right (k-1) hpos
    omega
  have hkpos : 0 < k := by omega
  have hk' : 2^W = 2^(j+1)*(k-1) + 2^(j+1) := by
    calc
      _ = 2^(j+1)*k := hk
      _ = 2^(j+1)*((k-1)+1) := by congr 1; omega
      _ = _ := by rw [Nat.mul_add,Nat.mul_one]
  omega

/-- All resets have a common right-register operation. `a=0,1` is the
    old phase bit and `m` the right counter at the collision. -/
def resetRight (a m e : Nat) := (4*m+1+2*a)*2^e

theorem reset_width {a n w z e : Nat} (ha : a ≤ 1) (hw : RightWidth n w)
    (hz : z < gap n w) : RightWidth (resetRight a (n+z) e) (w+e+2) := by
  have hpow : 2^(w+e+2) = 4*2^w*2^e := by
    rw [Nat.pow_add, Nat.pow_add]; change 2^w*2^e*4 = _; ac_rfl
  have hpow' : 2^(w+e+2-1) = 4*2^(w-1)*2^e := by
    have hwpos := hw.1
    have hidx : w+e+2-1 = (w-1)+e+2 := by omega
    rw [hidx,Nat.pow_add,Nat.pow_add]; change 2^(w-1)*2^e*4 = _; ac_rfl
  have hl : 4*2^(w-1) ≤ 4*(n+z)+1+2*a := by have h := hw.2.1; omega
  have hh : 4*(n+z)+1+2*a < 4*2^w := by unfold gap at hz; omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [hpow']; exact Nat.mul_le_mul_right _ hl
  · rw [hpow]; exact (Nat.mul_lt_mul_right (Nat.two_pow_pos e)).2 hh

theorem reset_gap {a n w z e : Nat} (ha : a ≤ 1) (hw : RightWidth n w)
    (hz : z < gap n w) :
    gap (resetRight a (n+z) e) (w+e+2) = (4*(gap n w-z)-1-2*a)*2^e := by
  have hp : 2^(w+e+2) = 4*2^w*2^e := by rw [Nat.pow_add,Nat.pow_add]; change 2^w*2^e*4 = _; ac_rfl
  unfold gap resetRight
  rw [hp, ← Nat.sub_mul]
  congr 1
  unfold gap at hz
  omega

theorem reset12_safe {a N n w j Q e : Nat} (ha : a ≤ 1)
    (hw : RightWidth n w) (hn : N < n) (ht : N < gap n w)
    (hf : N = 2^j*(2*Q+1)) :
    let z := 2^j-1
    let n' := resetRight a (n+z) e
    let w' := w+e+2
    RightWidth n' w' ∧ Q < n' ∧ Q < gap n' w' ∧ NonPower (gap n' w') := by
  dsimp
  obtain ⟨hz,hbudget⟩ := shifted12_budget hf ht
  have hp := Nat.two_pow_pos e
  have hj := Nat.two_pow_pos j
  have hq : Q < N := by
    have h : 2*Q+1 ≤ 2^j*(2*Q+1) := by simpa using Nat.mul_le_mul_right (2*Q+1) hj
    omega
  have hsmall : Q < 4*(n+(2^j-1))+1+2*a := by omega
  have hmul : 4*(n+(2^j-1))+1+2*a ≤ resetRight a (n+(2^j-1)) e := by
    unfold resetRight; simpa using Nat.mul_le_mul_left (4*(n+(2^j-1))+1+2*a) hp
  have hgap := reset_gap (e:=e) ha hw hz
  have hcoef : Q < 4*(gap n w-(2^j-1))-1-2*a := by omega
  have hmul' : 4*(gap n w-(2^j-1))-1-2*a ≤ (4*(gap n w-(2^j-1))-1-2*a)*2^e := by
    simpa using Nat.mul_le_mul_left (4*(gap n w-(2^j-1))-1-2*a) hp
  refine ⟨reset_width ha hw hz, by omega, by omega, ?_⟩
  rw [hgap]
  refine ⟨e,2*(gap n w-(2^j-1))-1-a,by omega,?_⟩
  rw [Nat.mul_comm]
  congr 1
  omega

theorem reset4_safe {N W j Q e : Nat} (hf : N = 2^j*(2*Q+1))
    (ht : N < 2^W) (hN : NonPower N) :
    let n := 2^W
    let w := W+1
    let z := 2^(j+1)-1
    let n' := resetRight 0 (n+z) e
    let w' := w+e+2
    RightWidth n' w' ∧ 0 < Q ∧ Q < n' ∧ Q < gap n' w' ∧ NonPower (gap n' w') := by
  dsimp
  have hw : RightWidth (2^W) (W+1) := by
    simp [RightWidth,Nat.pow_succ]; have hp := Nat.two_pow_pos W; omega
  have hg : gap (2^W) (W+1) = 2^W := by simp [gap,Nat.pow_succ]; omega
  obtain ⟨hz,hbudget⟩ := shifted4_budget hf ht
  rw [← hg] at hz hbudget
  have hq := factor_nonzero_tail hN hf
  have hp := Nat.two_pow_pos e
  have hj := Nat.two_pow_pos j
  have hqN : Q < N := by
    have h : 2*Q+1 ≤ 2^j*(2*Q+1) := by simpa using Nat.mul_le_mul_right (2*Q+1) hj
    omega
  have hmul : 4*(2^W+(2^(j+1)-1))+1 ≤ resetRight 0 (2^W+(2^(j+1)-1)) e := by
    unfold resetRight; simpa using Nat.mul_le_mul_left (4*(2^W+(2^(j+1)-1))+1) hp
  have hgap := reset_gap (e:=e) (by decide : 0 ≤ 1) hw hz
  have hcoef : Q < 4*(gap (2^W) (W+1)-(2^(j+1)-1))-1 := by omega
  have hmul' : 4*(gap (2^W) (W+1)-(2^(j+1)-1))-1 ≤
      (4*(gap (2^W) (W+1)-(2^(j+1)-1))-1)*2^e := by
    simpa using Nat.mul_le_mul_left (4*(gap (2^W) (W+1)-(2^(j+1)-1))-1) hp
  simp only [Nat.mul_zero,Nat.sub_zero] at hgap
  refine ⟨reset_width (by decide) hw hz,hq,by omega,by omega,?_⟩
  rw [hgap]
  refine ⟨e,2*(gap (2^W) (W+1)-(2^(j+1)-1))-1,by omega,?_⟩
  rw [Nat.mul_comm]; congr 1; omega

#print axioms nonPower_not_pow
#print axioms standard_zero_overflow
#print axioms standard_one_overflow
#print axioms shifted12_budget
#print axioms shifted4_budget
#print axioms reset12_safe
#print axioms reset4_safe
end BB6.Agent32F418.Arithmetic
