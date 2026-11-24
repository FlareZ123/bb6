import Std

namespace BB6.Agent32F418.ReturnBounds

/-- Low-first list of odd collision valuations, ending in the first even one.
    `more r` denotes valuation `2*r+1`; `last r` denotes `2*r`. -/
inductive Prefix where
  | last (r : Nat)
  | more (r : Nat) (tail : Prefix)
  deriving Repr, DecidableEq

namespace Prefix

def p : Prefix → Nat
  | last r => r
  | more r t => r+1+t.p

def E (b : Prefix) := 5*b.p+2
def L (b : Prefix) := 2*b.p+1

/-- Exact right-counter correction on a phase-1 normal episode. -/
def C : Prefix → Nat
  | last r => (2^(2*r+2)-1)*2^(5*r)
  | more r t => (2^(2*r+3)-1)*2^(5*r+3+t.E) + t.C

def value : Prefix → Nat → Nat
  | last r, Q => 2^(2*r)*(2*Q+1)
  | more r t, Q => 2^(2*r+1)*(2*t.value Q+1)

@[simp] theorem E_last (r : Nat) : (last r).E = 5*r+2 := rfl
@[simp] theorem E_more (r : Nat) (t : Prefix) :
    (more r t).E = 5*r+5+t.E := by simp [E,p]; omega
@[simp] theorem L_last (r : Nat) : (last r).L = 2*r+1 := rfl
@[simp] theorem L_more (r : Nat) (t : Prefix) :
    (more r t).L = 2*r+2+t.L := by simp [L,p]; omega

theorem pow_mono {a b : Nat} (h : a ≤ b) : 2^a ≤ 2^b :=
  Nat.pow_le_pow_right (by decide) h

theorem value_bounds (b : Prefix) (Q : Nat) :
    2^b.L*Q < b.value Q ∧ b.value Q < 2^b.L*(Q+1) := by
  induction b with
  | last r =>
    simp only [value,L_last,Nat.pow_succ]
    have hp := Nat.two_pow_pos (2*r)
    rw [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  | more r t ih =>
    simp only [value,L_more]
    have hp := Nat.two_pow_pos (2*r+1)
    have hpow : 2^(2*r+2+t.L) = 2^(2*r+1)*2*2^t.L := by
      rw [show 2*r+2+t.L = (2*r+1)+1+t.L by omega, Nat.pow_add,Nat.pow_succ]
    rw [hpow]
    obtain ⟨hl,hu⟩ := ih
    have hl' : 2*(2^t.L*Q) < 2*t.value Q+1 := by omega
    have hu' : 2*t.value Q+1 < 2*(2^t.L*(Q+1)) := by omega
    constructor
    · rw [Nat.mul_assoc, Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left hl' hp
    · rw [Nat.mul_assoc,Nat.mul_assoc]
      exact Nat.mul_lt_mul_of_pos_left hu' hp

private theorem more_upper_of_tail (r : Nat) (t : Prefix)
    (ih : t.C < 2^(t.E+2*t.p)) :
    (more r t).C < 2^((more r t).E+2*(more r t).p-1) := by
  let X := 2^(2*r+3)
  let Y := 2^(2*t.p)
  let K := 2^(5*r+3+t.E)
  have hx : 0 < X := Nat.two_pow_pos _
  have hy : 0 < Y := Nat.two_pow_pos _
  have hK : t.C < Y*K := by
    have hh : 2^(t.E+2*t.p) ≤ Y*K := by
      dsimp [Y,K]
      rw [←Nat.pow_add]
      exact pow_mono (by omega)
    exact Nat.lt_of_lt_of_le ih hh
  have hXY : X-1+Y ≤ X*Y := by
    have h1 : X-1 ≤ (X-1)*Y := by simpa using Nat.mul_le_mul_left (X-1) hy
    have h2 : X*Y = (X-1)*Y+Y := by
      calc
        X*Y = (X-1+1)*Y := by congr 1; omega
        _ = (X-1)*Y+Y := by rw [Nat.add_mul,Nat.one_mul]
    omega
  have hsum : (X-1)*K+t.C < (X-1+Y)*K := by rw [Nat.add_mul]; omega
  have hlt := Nat.lt_of_lt_of_le hsum (Nat.mul_le_mul_right K hXY)
  have hpow : X*Y*K = 2^((more r t).E+2*(more r t).p-1) := by
    dsimp [X,Y,K]
    rw [←Nat.pow_add,←Nat.pow_add]
    congr 1
    simp [E,p]
    omega
  rw [←hpow]
  exact hlt

theorem correction_upper (b : Prefix) : b.C < 2^(b.E+2*b.p) := by
  induction b with
  | last r =>
    simp only [C,E_last,p]
    calc
      (2^(2*r+2)-1)*2^(5*r) < 2^(2*r+2)*2^(5*r) :=
        Nat.mul_lt_mul_of_pos_right (by have h := Nat.two_pow_pos (2*r+2); omega) (Nat.two_pow_pos _)
      _ = 2^(5*r+2+2*r) := by rw [←Nat.pow_add]; congr 1; omega
  | more r t ih =>
    exact Nat.lt_of_lt_of_le (more_upper_of_tail r t ih) (pow_mono (by omega))

theorem correction_more_upper (r : Nat) (t : Prefix) :
    (more r t).C < 2^((more r t).E+2*(more r t).p-1) :=
  more_upper_of_tail r t (correction_upper t)

theorem correction_lower (b : Prefix) : 3*2^(b.E-2) ≤ b.C := by
  cases b with
  | last r =>
    simp only [E_last,C,Nat.add_sub_cancel]
    exact Nat.mul_le_mul_right _ (by
      have h := pow_mono (show 2 ≤ 2*r+2 by omega)
      change 4 ≤ 2^(2*r+2) at h
      omega)
  | more r t =>
    simp only [E_more,C]
    rw [show 5*r+5+t.E-2 = 5*r+3+t.E by omega]
    have h := pow_mono (show 2 ≤ 2*r+3 by omega)
    change 4 ≤ 2^(2*r+3) at h
    have h' := Nat.mul_le_mul_right (2^(5*r+3+t.E)) (show 3 ≤ 2^(2*r+3)-1 by omega)
    omega

theorem correction_gt_pow {b : Prefix} (hp : 0 < b.p) : 2^b.E < b.C := by
  cases b with
  | last r =>
    have hr : 0 < r := hp
    simp only [E_last,C]
    have h := pow_mono (show 4 ≤ 2*r+2 by omega)
    change 16 ≤ 2^(2*r+2) at h
    calc
      2^(5*r+2) = 4*2^(5*r) := by rw [Nat.pow_add,Nat.mul_comm]
      _ < (2^(2*r+2)-1)*2^(5*r) :=
        Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
  | more r t =>
    simp only [E_more,C]
    rw [show 5*r+5+t.E = (5*r+3+t.E)+2 by omega,Nat.pow_add,Nat.mul_comm (2^(5*r+3+t.E)) (2^2)]
    have h := pow_mono (show 3 ≤ 2*r+3 by omega)
    change 8 ≤ 2^(2*r+3) at h
    have h' := Nat.mul_lt_mul_of_pos_right (show 4 < 2^(2*r+3)-1 by omega) (Nat.two_pow_pos (5*r+3+t.E))
    exact Nat.lt_of_lt_of_le h' (Nat.le_add_right _ _)


theorem value_ge_last (b : Prefix) (Q : Nat) : 2^(b.L-1) ≤ b.value Q := by
  induction b with
  | last r =>
    simp only [value,L_last,Nat.add_sub_cancel]
    simpa using Nat.mul_le_mul_left (2^(2*r)) (show 1 ≤ 2*Q+1 by omega)
  | more r t ih =>
    simp only [value,L_more]
    have ht : 0 < t.L := by simp [L]
    have he : 2*r+2+t.L-1 = (2*r+1)+1+(t.L-1) := by omega
    rw [he,Nat.pow_add,Nat.pow_succ,Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    omega

theorem width_tail {b : Prefix} {Q W : Nat} (h : b.value Q < 2^W) :
    b.L ≤ W ∧ Q < 2^(W-b.L) := by
  have hlast := value_ge_last b Q
  have hlt := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 (show 2^(b.L-1) < 2^W by omega)
  have hL : 0 < b.L := by simp [L]
  have hLW : b.L ≤ W := by omega
  have hp : 2^W = 2^b.L*2^(W-b.L) := by
    rw [←Nat.pow_add,show b.L+(W-b.L)=W by omega]
  have hQ := (value_bounds b Q).1
  rw [hp] at h
  exact ⟨hLW, (Nat.mul_lt_mul_left (Nat.two_pow_pos b.L)).1 (by omega)⟩

def next (b : Prefix) (Q W : Nat) := 2^(W+b.E)+Q-b.C

def NoEven (N : Nat) : Prop := ∀ i, i%2=0 → N.testBit i = false

theorem two_top_bits {N h : Nat} (hl : 3*2^h ≤ N) (hu : N < 4*2^h) :
    N.testBit h = true ∧ N.testBit (h+1) = true := by
  have hdiv : N / 2^h = 3 := Nat.div_eq_of_lt_le hl hu
  have hpow : 2^(h+1)=2*2^h := by rw [Nat.pow_succ,Nat.mul_comm]
  have hdiv' : N / 2^(h+1) = 1 := by
    apply Nat.div_eq_of_lt_le
    · rw [hpow]; omega
    · rw [hpow]; omega
  simp [Nat.testBit_eq_decide_div_mod_eq,hdiv,hdiv']

theorem top_pair_not_noEven {N h : Nat} (hl : 3*2^h ≤ N) (hu : N < 4*2^h) :
    ¬NoEven N := by
  intro hn
  obtain ⟨h0,h1⟩ := two_top_bits hl hu
  by_cases he : h%2=0
  · rw [hn h he] at h0; contradiction
  · rw [hn (h+1) (by omega)] at h1; contradiction

/-- A borrow from the newly injected top power creates adjacent high 1s whenever
    the correction is strictly smaller than one quarter of that power. -/
theorem borrow_top_pair {b : Prefix} {Q W : Nat} (hwidth : b.value Q < 2^W)
    (hb : Q < b.C) (hc : b.C < 2^(W+b.E-2)) :
    ¬NoEven (b.next Q W) := by
  have hL := (width_tail hwidth).1
  have hLpos : 0 < b.L := by simp [L]
  have hE : 2 ≤ b.E := by simp [E]
  have hp : 2^(W+b.E) = 4*2^(W+b.E-2) := by
    rw [←Nat.pow_add (a:=2) (m:=2) (n:=W+b.E-2)]
    congr 1
    omega
  unfold next
  rw [hp]
  exact top_pair_not_noEven (h:=W+b.E-2) (by omega) (by omega)

theorem borrow_pair_of_spare_width {b : Prefix} {Q W : Nat}
    (hwidth : b.value Q < 2^W) (hb : Q < b.C) (hspare : b.L < W) :
    ¬NoEven (b.next Q W) := by
  apply borrow_top_pair hwidth hb
  exact Nat.lt_of_lt_of_le (correction_upper b) (pow_mono (by simp [L] at hspare; omega))

theorem borrow_pair_of_more {r Q W : Nat} {t : Prefix}
    (hwidth : (more r t).value Q < 2^W) (hb : Q < (more r t).C) :
    ¬NoEven ((more r t).next Q W) := by
  have hL := (width_tail hwidth).1
  apply borrow_top_pair hwidth hb
  exact Nat.lt_of_lt_of_le (correction_more_upper r t) (pow_mono (by simp [L] at hL; omega))

theorem singleton_at_width {r Q W : Nat}
    (hwidth : (last r).value Q < 2^W) (hW : W = 2*r+1) : Q=0 := by
  have hQ := (width_tail hwidth).2
  simp [L_last,hW] at hQ
  omega

theorem singleton_next (r : Nat) :
    (last r).next 0 (2*r+1) = 2^(5*r)*(2^(2*r+2)+1) := by
  simp only [next,E_last,C,Nat.add_zero]
  have hpow : 2^(2*r+1+(5*r+2)) = 2^(5*r)*2^(2*r+3) := by
    rw [←Nat.pow_add]; congr 1; omega
  rw [hpow,Nat.mul_comm (2^(2*r+2)-1) (2^(5*r)),←Nat.mul_sub]
  congr 1
  have hh : 2^(2*r+3)=2*2^(2*r+2) := by
    rw [show 2*r+3=(2*r+2)+1 by omega,Nat.pow_succ,Nat.mul_comm]
  have hp := Nat.two_pow_pos (2*r+2)
  omega

theorem singleton_noEven_requires_odd {r : Nat}
    (h : NoEven ((last r).next 0 (2*r+1))) : r%2=1 := by
  have hbit : ((last r).next 0 (2*r+1)).testBit (5*r) = true := by
    rw [singleton_next,Nat.testBit_eq_decide_div_mod_eq,Nat.mul_comm,Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
    have hh : 2^(2*r+2)=2^(2*r+1)*2 := by
      rw [show 2*r+2=(2*r+1)+1 by omega,Nat.pow_succ]
    rw [hh]
    simp
  by_cases hr : r%2=1
  · exact hr
  · have he : (5*r)%2=0 := by omega
    rw [h (5*r) he] at hbit
    contradiction

/-- Every borrow-caused odd-only output has the single possible input shape:
    a singleton at the very top of the old width, with odd half-index. -/
theorem oddOnly_borrow_predecessor {b : Prefix} {Q W : Nat}
    (hwidth : b.value Q < 2^W) (hb : Q < b.C) (hn : NoEven (b.next Q W)) :
    ∃ r, b=last r ∧ W=2*r+1 ∧ Q=0 ∧ r%2=1 := by
  have hL := (width_tail hwidth).1
  have heq : b.L=W := by
    by_cases hh : b.L=W
    · exact hh
    · exact False.elim (borrow_pair_of_spare_width hwidth hb (by omega) hn)
  cases b with
  | more r t => exact False.elim (borrow_pair_of_more hwidth hb hn)
  | last r =>
    have hW : W=2*r+1 := by simpa using heq.symm
    have hQ := singleton_at_width hwidth hW
    subst W
    subst Q
    exact ⟨r,rfl,rfl,rfl,singleton_noEven_requires_odd hn⟩

/-- Nonborrow returns have an isolated newly inserted top bit. -/
theorem noBorrow_top {b : Prefix} {Q W : Nat} (hwidth : b.value Q < 2^W)
    (hb : b.C ≤ Q) :
    ∃ R, R < 2^(W-b.L) ∧ b.next Q W = 2^(W+b.E)+R ∧
      (b.next Q W).testBit (W+b.E) = true := by
  have hQ := (width_tail hwidth).2
  have hR : Q-b.C < 2^(W-b.L) := by omega
  have hR' : Q-b.C < 2^(W+b.E) := Nat.lt_of_lt_of_le hR (pow_mono (by omega))
  have hEq : b.next Q W=2^(W+b.E)+(Q-b.C) := by unfold next; omega
  refine ⟨Q-b.C,hR,hEq,?_⟩
  rw [hEq]
  exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) (by
    rw [Nat.pow_succ]; omega)

theorem noBorrow_width {b : Prefix} {Q W : Nat} (hwidth : b.value Q < 2^W)
    (hb : b.C ≤ Q) (hp : 0 < b.p) : 7*b.p+4 ≤ W := by
  have hQ := (width_tail hwidth).2
  have hC := correction_gt_pow hp
  have hh : 2^b.E < 2^(W-b.L) := by omega
  have he := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).1 hh
  simp [E,L] at he
  omega

theorem oddOnly_noBorrow_predecessor {b : Prefix} {Q W : Nat}
    (hwidth : b.value Q < 2^W) (hb : b.C ≤ Q) (hn : NoEven (b.next Q W)) :
    (W+b.p)%2=1 ∧ (0 < b.p → 7*b.p+4 ≤ W) := by
  obtain ⟨R,hR,hEq,hbit⟩ := noBorrow_top hwidth hb
  have hpar : (W+b.E)%2=1 := by
    by_cases hh : (W+b.E)%2=1
    · exact hh
    · rw [hn (W+b.E) (by omega)] at hbit
      contradiction
  exact ⟨by simp [E] at hpar; omega,fun hp => noBorrow_width hwidth hb hp⟩

#print axioms value_bounds
#print axioms correction_upper
#print axioms correction_more_upper
#print axioms correction_lower
#print axioms correction_gt_pow
#print axioms oddOnly_borrow_predecessor
#print axioms oddOnly_noBorrow_predecessor

end Prefix
end BB6.Agent32F418.ReturnBounds
