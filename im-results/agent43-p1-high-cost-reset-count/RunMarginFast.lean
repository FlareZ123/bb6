import RunMargin

namespace BB6.Agent43P1Complement
open BB6.Agent45.DelayedCarry

/-- Doubling produces a window of 2^k bits in k packed operations. -/
def windowOrPow (X : Nat) : Nat → Nat
  | 0 => X
  | k+1 => let w := windowOrPow X k; w ||| (w >>> 2^k)

def windowAndPow (X : Nat) : Nat → Nat
  | 0 => X
  | k+1 => let w := windowAndPow X k; w &&& (w >>> 2^k)

theorem windowOrPow_iff (X k i : Nat) : (windowOrPow X k).testBit i=true ↔
    ∃ j, j<2^k ∧ X.testBit (i+j)=true := by
  induction k generalizing i with
  | zero => simp [windowOrPow]
  | succ k ih =>
    simp only [windowOrPow,Nat.testBit_or,Nat.testBit_shiftRight,Bool.or_eq_true,ih,Nat.pow_succ]
    constructor
    · rintro (⟨j,hj,hb⟩|⟨j,hj,hb⟩)
      · exact ⟨j,by omega,hb⟩
      · exact ⟨2^k+j,by omega,by simpa [show i+(2^k+j)=2^k+i+j by omega] using hb⟩
    · rintro ⟨j,hj,hb⟩
      by_cases h : j<2^k
      · exact Or.inl ⟨j,h,hb⟩
      · exact Or.inr ⟨j-2^k,by omega,by simpa [show 2^k+i+(j-2^k)=i+j by omega] using hb⟩

theorem windowAndPow_iff (X k i : Nat) : (windowAndPow X k).testBit i=false ↔
    ∃ j, j<2^k ∧ X.testBit (i+j)=false := by
  induction k generalizing i with
  | zero => simp [windowAndPow]
  | succ k ih =>
    simp only [windowAndPow,Nat.testBit_and,Nat.testBit_shiftRight,Bool.and_eq_false_iff,ih,Nat.pow_succ]
    constructor
    · rintro (⟨j,hj,hb⟩|⟨j,hj,hb⟩)
      · exact ⟨j,by omega,hb⟩
      · exact ⟨2^k+j,by omega,by simpa [show i+(2^k+j)=2^k+i+j by omega] using hb⟩
    · rintro ⟨j,hj,hb⟩
      by_cases h : j<2^k
      · exact Or.inl ⟨j,h,hb⟩
      · exact Or.inr ⟨j-2^k,by omega,by simpa [show 2^k+i+(j-2^k)=i+j by omega] using hb⟩

def PowRunOK (t k X : Nat) : Prop :=
    let m := 2^(t+1-2^k)-1
    windowOrPow X k &&& m=m ∧ windowAndPow X k &&& m=0

instance (t k X : Nat) : Decidable (PowRunOK t k X) := by unfold PowRunOK; infer_instance

theorem powRunOK_bits (t k X i : Nat) (h : PowRunOK t k X) (hi : i+2^k≤t) :
    (∃ j, j<2^k ∧ X.testBit (i+j)=true) ∧
    (∃ j, j<2^k ∧ X.testBit (i+j)=false) := by
  obtain ⟨hor,hand⟩ := h
  have ho := congrArg (fun x : Nat => x.testBit i) hor
  have ha := congrArg (fun x : Nat => x.testBit i) hand
  simp [show i<t+1-2^k by omega] at ho ha
  exact ⟨(windowOrPow_iff X k i).mp ho,(windowAndPow_iff X k i).mp ha⟩

theorem powRunOK_resMin (t k C j : Nat) (ho : C%2=1) (hj : 1≤j) (hjt : j≤t)
    (h : PowRunOK t k (7*C)) : 2^(j-2^k)≤resMin j C := by
  by_cases hgj : 2^k≤j
  · obtain ⟨h1,h0⟩ := powRunOK_bits t k (7*C) (j-2^k) h (by omega)
    exact mixed_margin j (2^k) (7*C) (Nat.two_pow_pos _) hgj h1 h0
  · have hd : 2 ∣ (2:Nat)^j := by simpa using Nat.pow_dvd_pow 2 hj
    have hm : ((7*C)%2^j)%2=1 := by rw [Nat.mod_mod_of_dvd _ hd,Nat.mul_mod]; simp [ho]
    have hlt : (7*C)%2^j<2^j := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [show j-2^k=0 by omega,Nat.pow_zero]
    unfold resMin
    exact Nat.le_min.mpr ⟨by omega,by omega⟩

theorem powRunOK_margin (n K t k C j : Nat) (ho : C%2=1) (hj : 1≤j) (hjt : j≤t)
    (h : PowRunOK t k (7*C)) (hgn : 2^k≤n)
    (hsafe : (n+K+2)*marginSize n K<6*2^(n-2^k)) :
    (n+K+2)*marginSize n K*2^j<6*2^n*resMin j C := by
  have hmin := powRunOK_resMin t k C j ho hj hjt h
  have hmul := Nat.mul_lt_mul_of_pos_right hsafe (Nat.two_pow_pos j)
  have hexp : n-2^k+j≤n+(j-2^k) := by omega
  have hpow := Nat.pow_le_pow_right (show 0<2 by decide) hexp
  have hle : 6*2^(n-2^k)*2^j≤6*2^n*2^(j-2^k) := by
    rw [Nat.mul_assoc,←Nat.pow_add,Nat.mul_assoc,←Nat.pow_add]
    exact Nat.mul_le_mul_left 6 hpow
  exact Nat.lt_of_lt_of_le hmul (Nat.le_trans hle (Nat.mul_le_mul_left _ hmin))

theorem allBlockMargins_of_powRunOK (n K s h k : Nat) (qs : List Prefix)
    (hgn : 2^k≤n) (hsafe : (n+K+2)*marginSize n K<6*2^(n-2^k))
    (hcheck : ∀ C c, (C,c)∈qs → C%2=1 ∧ PowRunOK (s+h) k (7*C)) :
    AllBlockMargins n K s h qs := by
  intro C c hc j hj hjt
  obtain ⟨ho,hrun⟩ := hcheck C c hc
  exact powRunOK_margin n K (s+h) k C j ho (by omega) hjt hrun hgn hsafe

#print axioms windowOrPow_iff
#print axioms windowAndPow_iff
#print axioms allBlockMargins_of_powRunOK
end BB6.Agent43P1Complement
