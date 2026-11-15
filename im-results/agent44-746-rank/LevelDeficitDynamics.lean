import FirstInverseComplete

set_option maxHeartbeats 0

/-!
Exact deficit coordinates for the genuine #746 first-reset map.

At a first-failure level k, put D = 8*2^k + k - h.  An even reset
halves D; it remains at level k exactly while D > 4*k+10.  An odd
reset is encoded by q = 8*2^k - A, where
A = (D-2*k-5)/2.  Since q=2^t*d with d odd and 0<q<2^(k+3),
the odd-exit exponent t is exactly the 2-adic valuation of A.
-/

namespace CascadeLevelDeficit

open CascadeResetInverse

def deficit (h k : Nat) : Nat := 8*2^k + k - h

def evenOutput (h k : Nat) : Nat := 4*2^k + (h+k)/2

def oddParameter (h k : Nat) : Nat := 4*2^k + (h+k)/2 + 3

def oddOutput (t d : Nat) : Nat := (3^(t+1)*d-5)/2

def oddOffset (h k : Nat) : Nat := 8*2^k - oddParameter h k

private theorem pow_two_mono (m n : Nat) (hmn : m ≤ n) :
    2^m ≤ 2^n := by
  induction n with
  | zero =>
      have : m=0 := by omega
      subst m
      exact Nat.le_refl _
  | succ n ih =>
      by_cases h : m ≤ n
      · have hp := ih h
        rw [Nat.pow_succ]
        omega
      · have hm : m=n+1 := by omega
        subst m
        exact Nat.le_refl _

private theorem pow_two_le_three (t : Nat) : 2^t ≤ 3^t := by
  induction t with
  | zero => decide
  | succ t ih =>
      rw [Nat.pow_succ, Nat.pow_succ]
      omega

private theorem k_add_three_lt_eight_pow (k : Nat) :
    k+3 < 8*2^k := by
  induction k with
  | zero => decide
  | succ k ih =>
      rw [Nat.pow_succ]
      omega

private theorem four_mul_pow_two_even (k : Nat) :
    (4*2^k)%2=0 := by
  simp [Nat.mul_mod]

/-- A pair of first-failure certificates for the same height has the
same level. -/
theorem first_fail_unique (h k l : Nat)
    (hk : (∀ j, j<k → 8*2^j≤h+j+5) ∧ h+k+5<8*2^k)
    (hl : (∀ j, j<l → 8*2^j≤h+j+5) ∧ h+l+5<8*2^l) :
    k=l := by
  by_cases hkl : k<l
  · have hguard := hl.1 k hkl
    omega
  · by_cases hlk : l<k
    · have hguard := hk.1 l hlk
      omega
    · omega

/-- The exact even reset identity: the level deficit is halved. -/
theorem even_deficit_halves (h k : Nat)
    (hpar : (h+k)%2=0) :
    deficit h k = 2*deficit (evenOutput h k) k := by
  have hdiv : h+k=2*((h+k)/2) := by omega
  dsimp [deficit,evenOutput]
  omega

/-- An even reset remains at the same first-failure level exactly when
the current deficit exceeds 4*k+10. All earlier sweep guards persist. -/
theorem even_level_criterion (h k : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=0) :
    (∀ j, j<k → 8*2^j≤evenOutput h k+j+5) ∧
    ((evenOutput h k+k+5<8*2^k) ↔ deficit h k>4*k+10) := by
  have h2u : 2*evenOutput h k=8*2^k+h+k := by
    have hdiv : h+k=2*((h+k)/2) := by omega
    dsimp [evenOutput]
    omega
  have hDpos : 6≤8*2^k+k-h := by omega
  have hgt : h≤evenOutput h k := by omega
  constructor
  · intro j hj
    have hguard := hg j hj
    omega
  · constructor
    · intro hu
      dsimp [deficit]
      omega
    · intro hD
      dsimp [deficit] at hD
      omega

/-- If the even-reset deficit is at most 4*k+10, the even reset exits
to exactly level k+1. -/
theorem even_next_level (h k : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=0)
    (hD : deficit h k≤4*k+10) :
    (∀ j, j<k+1 → 8*2^j≤evenOutput h k+j+5) ∧
      evenOutput h k+(k+1)+5<8*2^(k+1) := by
  have h2u : 2*evenOutput h k=8*2^k+h+k := by
    have hdiv : h+k=2*((h+k)/2) := by omega
    dsimp [evenOutput]
    omega
  have hgt : h≤evenOutput h k := by
    have hDpos : 6≤8*2^k+k-h := by omega
    omega
  have htop : evenOutput h k+3≤8*2^k := by omega
  have hpow : 8*2^(k+1)=16*2^k := by
    rw [Nat.pow_succ]
    omega
  constructor
  · intro j hj
    by_cases hjk : j<k
    · have hguard := hg j hjk
      omega
    · have hj_eq : j=k := by omega
      subst j
      dsimp [deficit] at hD
      omega
  · rw [hpow]
    have hlinear := k_add_three_lt_eight_pow k
    omega

/-- For an odd reset, every sweep guard through level k still succeeds
at the child height. Consequently its next first-failure level is
strictly greater than k. -/
theorem odd_reset_guards (h k t d : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=1)
    (hd : d%2=1)
    (hfactor : oddParameter h k=2^t*d) :
    ∀ j, j≤k → 8*2^j≤oddOutput t d+j+5 := by
  have hlow := first_low h k hg
  have hnot : h+k+4≠4*2^k := by
    intro heq
    have hodd : (h+k+4)%2=1 := by omega
    rw [heq] at hodd
    simp [Nat.mul_mod] at hodd
  have hband := odd_inverse_band h k hlow hhigh hnot hpar
  have hqlo : 6*2^k+1≤oddParameter h k := by
    simpa [oddParameter] using hband.1.1
  have hqeq : oddParameter h k=2^t*d := hfactor
  have hdpos : 1≤d := by omega
  have hpow := pow_two_le_three t
  have hmul := Nat.mul_le_mul_right (3*d) hpow
  have h3q : 3*(2^t*d)≤3^(t+1)*d := by
    calc
      3*(2^t*d)=2^t*(3*d) := by ac_rfl
      _≤3^t*(3*d) := hmul
      _=3^(t+1)*d := by rw [Nat.pow_succ]; ac_rfl
  have hnum : 2*oddOutput t d+5=3^(t+1)*d :=
    odd_output_equation t d hd (by omega)
  have hnumlo : 18*2^k+3≤3^(t+1)*d := by
    rw [←hqeq] at h3q
    have hmullo := Nat.mul_le_mul_left 3 hqlo
    omega
  have huplus : 9*2^k≤oddOutput t d+1 := by omega
  have huge : 8*2^k≤oddOutput t d := by
    have hp : 1≤2^k := Nat.one_le_pow k 2 (by decide)
    omega
  intro j hj
  by_cases hsmall : j<k
  · have hguard := hg j hsmall
    omega
  · have hjeq : j=k := by omega
    subst j
    omega

/-- Any first-failure certificate for an odd-reset child lies strictly
above the source level. -/
theorem odd_reset_level_increases (h k t d k' : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=1)
    (hd : d%2=1)
    (hfactor : oddParameter h k=2^t*d)
    (hfail : oddOutput t d+k'+5<8*2^k') :
    k<k' := by
  have hall := odd_reset_guards h k t d hg hhigh hpar hd hfactor
  by_cases hle : k'≤k
  · have hguard := hall k' hle
    omega
  · omega

/-- The odd-reset parameter is 8*2^k minus a positive offset. -/
theorem odd_offset_bounds (h k : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=1) :
    1≤oddOffset h k ∧ oddOffset h k≤2^(k+1)-1 := by
  have hlow := first_low h k hg
  have hnot : h+k+4≠4*2^k := by
    intro heq
    have hodd : (h+k+4)%2=1 := by omega
    rw [heq] at hodd
    simp [Nat.mul_mod] at hodd
  have hband := odd_inverse_band h k hlow hhigh hnot hpar
  have hqlo : 6*2^k+1≤oddParameter h k := by
    simpa [oddParameter] using hband.1.1
  have hqhi : oddParameter h k≤8*2^k-1 := by
    simpa [oddParameter] using hband.1.2
  constructor
  · dsimp [oddOffset,oddParameter]
    omega
  · have hp : 2^(k+1)=2*2^k := by rw [Nat.pow_succ]; omega
    dsimp [oddOffset,oddParameter]
    omega

/-- Exact deficit-to-parameter identity at every odd exit:
D = 2*A + 2*k + 5. -/
theorem odd_deficit_identity (h k : Nat)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=1) :
    deficit h k=2*oddOffset h k+2*k+5 := by
  have hodd : h+k=2*((h+k)/2)+1 := by omega
  have hDpos : h≤8*2^k+k := by omega
  have hqpos : oddParameter h k≤8*2^k := by
    dsimp [oddParameter]
    omega
  dsimp [deficit,oddOffset,oddParameter]
  omega

/-- The valuation exponent t in q=2^t*d is exactly the 2-adic
valuation of A=8*2^k-q: A=2^t*a with a odd. -/
theorem odd_offset_factorization (h k t d : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=1)
    (hfactor : oddParameter h k=2^t*d)
    (hd : d%2=1) :
    ∃ a, oddOffset h k=2^t*a ∧ a%2=1 := by
  have hlow := first_low h k hg
  have hnot : h+k+4≠4*2^k := by
    intro heq
    have hodd : (h+k+4)%2=1 := by omega
    rw [heq] at hodd
    simp [Nat.mul_mod] at hodd
  have hband := odd_inverse_band h k hlow hhigh hnot hpar
  have hqlo : 6*2^k+1≤oddParameter h k := by
    simpa [oddParameter] using hband.1.1
  have hqhi : oddParameter h k≤8*2^k-1 := by
    simpa [oddParameter] using hband.1.2
  have hpow3 : 8*2^k=2^(k+3) := by
    calc
      8*2^k=2^3*2^k := by rfl
      _=2^(3+k) := by rw [Nat.pow_add]
      _=2^(k+3) := by congr 1; omega
  have hApos : 1≤oddOffset h k := by
    dsimp [oddOffset,oddParameter]
    omega
  have hq_lt : oddParameter h k<2^(k+3) := by
    rw [←hpow3]
    omega
  have hdpos : 1≤d := by omega
  have htwo_le_q : 2^t≤oddParameter h k := by
    rw [hfactor]
    have hm := Nat.mul_le_mul_left (2^t) hdpos
    simpa using hm
  have htbound : t≤k+2 := by
    by_cases ht : t≤k+2
    · exact ht
    · have ht' : k+3≤t := by omega
      have hmono := pow_two_mono (k+3) t ht'
      omega
  have hexp : t+(k+3-t)=k+3 := by omega
  have hpow : 2^(k+3)=2^t*2^(k+3-t) := by
    calc
      2^(k+3)=2^(t+(k+3-t)) := by rw [hexp]
      _=2^t*2^(k+3-t) := by rw [Nat.pow_add]
  have hdt : d<2^(k+3-t) := by
    by_cases hdlt : d<2^(k+3-t)
    · exact hdlt
    · have hle : 2^(k+3-t)≤d := by
        rcases Nat.lt_or_ge d (2^(k+3-t)) with hlt|hle
        · exact False.elim (hdlt hlt)
        · exact hle
      have hm := Nat.mul_le_mul_left (2^t) hle
      rw [←hpow] at hm
      rw [hfactor] at hq_lt
      omega
  have hpoweven : 2^(k+3-t)%2=0 := by
    have hexppos : 0<k+3-t := by omega
    cases he : k+3-t with
    | zero => omega
    | succ e =>
        simp [Nat.pow_succ]
  have hodd : (2^(k+3-t)-d)%2=1 := by omega
  have hsum :
      2^t*(2^(k+3-t)-d)+2^t*d=2^(k+3) := by
    calc
      _=2^t*((2^(k+3-t)-d)+d) := by rw [Nat.mul_add]
      _=2^t*2^(k+3-t) := by
        rw [Nat.sub_add_cancel (Nat.le_of_lt hdt)]
      _=2^(k+3) := hpow.symm
  have hAq : oddOffset h k+2^t*d=2^(k+3) := by
    change 8*2^k-oddParameter h k+2^t*d=2^(k+3)
    rw [hfactor,hpow3]
    omega
  have hAfac : oddOffset h k=2^t*(2^(k+3-t)-d) :=
    Nat.add_right_cancel (hAq.trans hsum.symm)
  exact ⟨2^(k+3-t)-d,hAfac,hodd⟩

/-- The exact source odd-reset output equation in deficit coordinates. -/
theorem odd_output_equation_deficit (h k t d : Nat)
    (hg : ∀ j, j<k → 8*2^j≤h+j+5)
    (hhigh : h+k+5<8*2^k)
    (hpar : (h+k)%2=1)
    (hfactor : oddParameter h k=2^t*d)
    (hd : d%2=1) :
    2*oddOutput t d+5=3^(t+1)*d ∧
    deficit h k=2*oddOffset h k+2*k+5 ∧
    (∃ a, oddOffset h k=2^t*a ∧ a%2=1) := by
  have hqlo : 7≤2^t*d := by
    have hlow := first_low h k hg
    have hnot : h+k+4≠4*2^k := by
      intro heq
      have hodd : (h+k+4)%2=1 := by omega
      rw [heq] at hodd
      simp [Nat.mul_mod] at hodd
    have hband := odd_inverse_band h k hlow hhigh hnot hpar
    have hqlo' : 6*2^k+1≤oddParameter h k := by
      simpa [oddParameter] using hband.1.1
    rw [hfactor] at hqlo'
    omega
  exact ⟨odd_output_equation t d hd hqlo,
    odd_deficit_identity h k hhigh hpar,
    odd_offset_factorization h k t d hg hhigh hpar hfactor hd⟩

#print axioms even_deficit_halves
#print axioms even_level_criterion
#print axioms even_next_level
#print axioms odd_reset_level_increases
#print axioms odd_offset_factorization
#print axioms odd_output_equation_deficit

end CascadeLevelDeficit
