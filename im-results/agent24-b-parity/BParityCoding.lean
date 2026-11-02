import Lean.Elab.Tactic.Omega

namespace BB6.Agent24.Coding

/-- The shift-conjugate of Machine B's scalar map. -/
def T (v : Nat) : Nat := (3*v + 7*(v%2))/2

def path (v : Nat) : Nat → Nat
  | 0 => v
  | i+1 => T (path v i)

theorem path_step (v i : Nat) :
    2*path v (i+1) = 3*path v i + 7*(path v i%2) := by
  dsimp [path,T]
  omega

theorem T_even_shift (a u : Nat) : T (a+2*u) = T a+3*u := by
  dsimp [T]
  omega

theorem path_succ_initial (a i : Nat) : path a (i+1) = path (T a) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
      change T (path a (i+1)) = T (path (T a) i)
      rw [ih]

/-- Exact sensitivity of n iterates to an arbitrary 2^n shift at input. -/
theorem path_shift_pow (a n t : Nat) :
    path (a+2^n*t) n = path a n + 3^n*t := by
  induction n generalizing a t with
  | zero => simp [path]
  | succ n ih =>
      have hfactor : 2^(n+1)*t=2*(2^n*t) := by
        rw [Nat.pow_succ]
        ac_rfl
      have hT : T (a+2^(n+1)*t) = T a + 2^n*(3*t) := by
        rw [hfactor]
        rw [T_even_shift]
        congr 1
        ac_rfl
      calc
        path (a+2^(n+1)*t) (n+1) = path (T (a+2^(n+1)*t)) n := path_succ_initial _ _
        _ = path (T a+2^n*(3*t)) n := by rw [hT]
        _ = path (T a) n + 3^n*(3*t) := ih (T a) (3*t)
        _ = path a (n+1) + 3^(n+1)*t := by
            rw [path_succ_initial, Nat.pow_succ]
            ac_rfl

/-- Matching length-n parity prefixes force initial values to coincide modulo 2^n. -/
theorem prefix_forces_divisor (a b n : Nat)
    (hab : a ≤ b)
    (hp : ∀ i : Nat, i < n → (path a i)%2 = (path b i)%2) :
    2^n ∣ b-a := by
  have ho : ∀ i : Nat, i ≤ n → path a i ≤ path b i := by
    intro i
    induction i with
    | zero =>
        intro _
        simpa [path] using hab
    | succ i ih =>
        intro hi
        have hi' : i < n := by omega
        have hprev := ih (by omega)
        have h1 := path_step a i
        have h2 := path_step b i
        have he := hp i hi'
        omega
  let d (i : Nat) : Nat := path b i - path a i
  have hd (i : Nat) (hi : i < n) : 2*d (i+1) = 3*d i := by
    have hprev := ho i (by omega)
    have hnext := ho (i+1) (by omega)
    have h1 := path_step a i
    have h2 := path_step b i
    have he := hp i hi
    dsimp [d]
    omega
  have hmul : ∀ i : Nat, i ≤ n → 2^i*d i = 3^i*d 0 := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
        intro hi
        have hi' : i < n := by omega
        have hp' := ih (by omega)
        calc
          2^(i+1)*d (i+1) = 2^i*(2*d (i+1)) := by rw [Nat.pow_succ]; ac_rfl
          _ = 2^i*(3*d i) := by rw [hd i hi']
          _ = 3*(2^i*d i) := by ac_rfl
          _ = 3*(3^i*d 0) := by rw [hp']
          _ = 3^(i+1)*d 0 := by rw [Nat.pow_succ]; ac_rfl
  have hdiv : 2^n ∣ d 0 := by
    apply (Nat.Coprime.pow n n (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_left
    exact ⟨d n, (hmul n (by omega)).symm⟩
  exact hdiv

/-- Congruence modulo 2^n also suffices for agreement of the first n bits. -/
theorem divisor_forces_prefix (a b n : Nat)
    (hab : a ≤ b) (hdiv : 2^n ∣ b-a) :
    ∀ i : Nat, i < n → (path a i)%2 = (path b i)%2 := by
  induction n generalizing a b with
  | zero =>
      intro i hi
      omega
  | succ n ih =>
      obtain ⟨t, ht⟩ := hdiv
      have hfactor : 2^(n+1)*t = 2*(2^n*t) := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hfactor] at ht
      have hb : b = a + 2*(2^n*t) := by omega
      have hpar : a%2=b%2 := by omega
      have hstepa : 2*T a = 3*a + 7*(a%2) := by dsimp [T]; omega
      have hstepb : 2*T b = 3*b + 7*(b%2) := by dsimp [T]; omega
      have hT : T b = T a + 3*(2^n*t) := by omega
      have horder : T a ≤ T b := by omega
      have hnext : 2^n ∣ T b - T a := by
        refine ⟨3*t, ?_⟩
        rw [hT]
        simp only [Nat.add_sub_cancel_left]
        ac_rfl
      intro i hi
      cases i with
      | zero => simpa [path] using hpar
      | succ i =>
          have hrest := ih (T a) (T b) horder hnext i (by omega)
          rw [path_succ_initial, path_succ_initial]
          exact hrest

/-- First-n parity words are equivalent to initial residue classes modulo 2^n. -/
theorem prefix_iff_congruent (a b n : Nat) (hab : a ≤ b) :
    (∀ i : Nat, i < n → (path a i)%2 = (path b i)%2) ↔ 2^n ∣ b-a := by
  constructor
  · exact prefix_forces_divisor a b n hab
  · exact divisor_forces_prefix a b n hab

theorem three_pow_odd (n : Nat) : (3^n)%2=1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- Adding the nth input bit flips precisely the nth parity output bit,
    while preserving all earlier parity bits. -/
theorem parity_bit_lift (a n : Nat) :
    (∀ i : Nat, i<n → (path (a+2^n) i)%2 = (path a i)%2) ∧
    (path (a+2^n) n)%2 ≠ (path a n)%2 := by
  constructor
  · intro i hi
    have ha : a ≤ a+2^n := Nat.le_add_right a (2^n)
    have hd : 2^n ∣ (a+2^n)-a := by simp
    have hp := divisor_forces_prefix a (a+2^n) n ha hd i hi
    exact hp.symm
  · have hs := path_shift_pow a n 1
    simp only [Nat.mul_one] at hs
    have ho := three_pow_odd n
    omega

/-- The full parity itinerary is injective on all natural starting states. -/
theorem full_itinerary_injective (a b : Nat)
    (hp : ∀ i : Nat, (path a i)%2 = (path b i)%2) : a = b := by
  by_cases hab : a ≤ b
  · by_cases heq : a=b
    · exact heq
    · have hpos : 0 < b-a := by omega
      have hdiv (n : Nat) : 2^n ∣ b-a :=
        prefix_forces_divisor a b n hab (by intro i _; exact hp i)
      have hle := Nat.le_of_dvd hpos (hdiv (b-a))
      have hgt : b-a < 2^(b-a) := Nat.lt_pow_self (by omega)
      omega
  · have hba : b ≤ a := by omega
    have hpos : 0 < a-b := by omega
    have hdiv (n : Nat) : 2^n ∣ a-b :=
      prefix_forces_divisor b a n hba (by intro i _; exact (hp i).symm)
    have hle := Nat.le_of_dvd hpos (hdiv (a-b))
    have hgt : a-b < 2^(a-b) := Nat.lt_pow_self (by omega)
    omega

/-- Two distinct inputs with gap less than 2^n have distinct length-n parity prefixes. -/
theorem finite_prefix_separates (a b n : Nat)
    (hab : a < b) (hgap : b-a < 2^n) :
    ∃ i : Nat, i < n ∧ (path a i)%2 ≠ (path b i)%2 := by
  classical
  by_cases hex : ∃ i : Nat, i < n ∧ (path a i)%2 ≠ (path b i)%2
  · exact hex
  · have hp (i : Nat) (hi : i < n) : path a i%2 = path b i%2 := by
      by_cases h : path a i%2 = path b i%2
      · exact h
      · exact False.elim (hex ⟨i,hi,h⟩)
    have hd := prefix_forces_divisor a b n (by omega) hp
    have hpos : 0 < b-a := by omega
    have hle := Nat.le_of_dvd hpos hd
    omega

#print axioms path_shift_pow
#print axioms parity_bit_lift
#print axioms divisor_forces_prefix
#print axioms prefix_iff_congruent
#print axioms prefix_forces_divisor
#print axioms full_itinerary_injective
#print axioms finite_prefix_separates
end BB6.Agent24.Coding
