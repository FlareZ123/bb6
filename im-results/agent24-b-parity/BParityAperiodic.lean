import Lean.Elab.Tactic.Omega

namespace BB6.Agent24

/-- The affine parity recurrence conjugate to the exact Machine B scalar map.
    If `z` is Agent 18's scalar coordinate, our `v = z + 8`. -/
def T (v : Nat) : Nat := (3*v + 7*(v%2))/2

def orbit : Nat → Nat
  | 0 => 8
  | n+1 => T (orbit n)

/-- Agent 18's two-branch scalar return map, copied exactly. -/
def G (z : Nat) : Nat := 3*(z/2) + 4 + 5*(z%2)

def gOrbit : Nat → Nat
  | 0 => 0
  | n+1 => G (gOrbit n)

/-- Agent 18's exact iterator orientation. -/
def iterG : Nat → Nat → Nat
  | 0,z => z
  | n+1,z => iterG n (G z)

theorem iterG_apply_G (n z : Nat) : iterG n (G z) = G (iterG n z) := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
      change iterG n (G (G z)) = G (iterG n (G z))
      exact ih (G z)

theorem gOrbit_eq_iterG (n : Nat) : gOrbit n = iterG n 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change G (gOrbit n) = iterG n (G 0)
      rw [ih, iterG_apply_G]

/-- Translation by eight conjugates the two affine recurrences. -/
theorem shift_identity (z : Nat) : T (z+8) = G z+8 := by
  dsimp [T, G]
  omega

theorem orbit_shift (n : Nat) : orbit n = gOrbit n + 8 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change T (orbit n) = G (gOrbit n) + 8
      rw [ih, shift_identity]

/-- An exact integral version of the affine recurrence. -/
theorem orbit_step (n : Nat) :
    2 * orbit (n+1) = 3*orbit n + 7*(orbit n%2) := by
  dsimp [orbit, T]
  omega

/-- A global congruence, independent of the parity itinerary. -/
theorem orbit_mod7_step (n : Nat) :
    orbit (n+1)%7 = (5*orbit n)%7 := by
  have h := orbit_step n
  omega

theorem orbit_mod7 (n : Nat) : orbit n%7 = (8*5^n)%7 := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
      rw [orbit_mod7_step]
      have hp : 8*5^(n+1) = 5*(8*5^n) := by
        rw [Nat.pow_succ]; omega
      rw [hp]
      omega

/-- This orbit grows strictly at every iteration. -/
theorem orbit_lower (n : Nat) : 8 ≤ orbit n := by
  induction n with
  | zero => simp [orbit]
  | succ n ih =>
      have h := orbit_step n
      omega

theorem orbit_inc (n : Nat) : orbit n < orbit (n+1) := by
  have h := orbit_step n
  have h8 := orbit_lower n
  omega

theorem orbit_le_shift (n k : Nat) : orbit n ≤ orbit (n+k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := orbit_inc (n+k)
    rw [Nat.add_succ]
    exact Nat.le_trans ih (Nat.le_of_lt h)

theorem orbit_lt_shift (n k : Nat) (hk : 0 < k) : orbit n < orbit (n+k) := by
  cases k with
  | zero => omega
  | succ k =>
      have h := orbit_inc (n+k)
      have hle := orbit_le_shift n k
      have hlt := Nat.lt_of_le_of_lt hle h
      rw [Nat.add_succ]
      exact hlt

/-- If a nonnegative integral sequence expands by an exact ratio 3/2
    at every step, the initial value must be zero. -/
theorem zero_of_two_three
    (d : Nat → Nat)
    (h : ∀ n, 2*d (n+1) = 3*d n) : d 0 = 0 := by
  have hmul (n : Nat) : 2^n*d n = 3^n*d 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        2^(n+1)*d (n+1) = 2^n*(2*d (n+1)) := by rw [Nat.pow_succ]; ac_rfl
        _ = 2^n*(3*d n) := by rw [h n]
        _ = 3*(2^n*d n) := by ac_rfl
        _ = 3*(3^n*d 0) := by rw [ih]
        _ = 3^(n+1)*d 0 := by rw [Nat.pow_succ]; ac_rfl
  have hdiv (n : Nat) : 2^n ∣ d 0 := by
    apply (Nat.Coprime.pow n n (by decide : Nat.Coprime 2 3)).dvd_of_dvd_mul_left
    exact ⟨d n, (hmul n).symm⟩
  by_cases heq : d 0 = 0
  · exact heq
  · have hpos : 0 < d 0 := Nat.pos_of_ne_zero heq
    have hsmall := Nat.le_of_dvd hpos (hdiv (d 0))
    have hlarge : d 0 < 2^(d 0) := Nat.lt_pow_self (by omega)
    omega

/-- The full infinite parity itinerary of Machine B's scalar orbit is not
    eventually periodic with any positive period. -/
theorem parity_not_eventually_periodic (N k : Nat) (hk : 0 < k) :
    ¬ (∀ n : Nat, orbit (N+n+k)%2 = orbit (N+n)%2) := by
  intro hperiod
  let d (n : Nat) : Nat := orbit (N+n+k) - orbit (N+n)
  have hpositive : 0 < d 0 := by
    dsimp [d]
    have hs := orbit_lt_shift N k hk
    omega
  have hdiff (n : Nat) : 2*d (n+1) = 3*d n := by
    have hu := orbit_step (N+n+k)
    have hl := orbit_step (N+n)
    have he := hperiod n
    have hstrict := orbit_lt_shift (N+n) k hk
    have hstrict' := orbit_lt_shift (N+(n+1)) k hk
    dsimp [d]
    have harg1 : (N + n + k + 1) = (N+(n+1)+k) := by omega
    have harg2 : (N + n + 1) = (N+(n+1)) := by omega
    rw [harg1] at hu
    rw [harg2] at hl
    omega
  have hz := zero_of_two_three d hdiff
  omega

/-- The parity itinerary of the unshifted two-branch Machine B model
    cannot be eventually periodic either. -/
theorem gparity_not_eventually_periodic (N k : Nat) (hk : 0 < k) :
    ¬ (∀ n : Nat, gOrbit (N+n+k)%2 = gOrbit (N+n)%2) := by
  intro h
  apply parity_not_eventually_periodic N k hk
  intro n
  have hh := h n
  rw [orbit_shift, orbit_shift]
  omega

/-- Same statement expressed using the iterator from Agent 18. -/
theorem iterG_not_eventually_periodic (N k : Nat) (hk : 0 < k) :
    ¬ (∀ n : Nat, (iterG (N+n+k) 0)%2 = (iterG (N+n) 0)%2) := by
  intro h
  apply gparity_not_eventually_periodic N k hk
  intro n
  rw [gOrbit_eq_iterG, gOrbit_eq_iterG]
  exact h n

theorem iterG_mod7 (n : Nat) :
    (iterG n 0+8)%7 = (8*5^n)%7 := by
  have h := orbit_mod7 n
  rw [orbit_shift, gOrbit_eq_iterG] at h
  exact h

/-- Adjacent opposite parity entries occur after every cutoff. -/
theorem parity_flip_after (N : Nat) :
    ∃ n : Nat, (iterG (N+n+1) 0)%2 ≠ (iterG (N+n) 0)%2 := by
  exact Classical.not_forall.mp (iterG_not_eventually_periodic N 1 (by omega))

/-- The unsampled scalar trajectory contains both parities infinitely often. -/
theorem both_parities_after (N : Nat) :
    (∃ n : Nat, N ≤ n ∧ (iterG n 0)%2 = 0) ∧
    (∃ n : Nat, N ≤ n ∧ (iterG n 0)%2 = 1) := by
  obtain ⟨n,hflip⟩ := parity_flip_after N
  have ha : (iterG (N+n+1) 0)%2 < 2 := Nat.mod_lt _ (by omega)
  have hb : (iterG (N+n) 0)%2 < 2 := Nat.mod_lt _ (by omega)
  have hcases : ((iterG (N+n+1) 0)%2=0 ∧ (iterG (N+n) 0)%2=1) ∨
      ((iterG (N+n+1) 0)%2=1 ∧ (iterG (N+n) 0)%2=0) := by omega
  rcases hcases with ⟨h0,h1⟩ | ⟨h1,h0⟩
  · exact ⟨⟨N+n+1, by omega, h0⟩, ⟨N+n, by omega, h1⟩⟩
  · exact ⟨⟨N+n, by omega, h0⟩, ⟨N+n+1, by omega, h1⟩⟩

#print axioms orbit_mod7
#print axioms orbit_shift
#print axioms parity_not_eventually_periodic
#print axioms gparity_not_eventually_periodic
#print axioms iterG_not_eventually_periodic
#print axioms iterG_mod7
#print axioms both_parities_after
end BB6.Agent24
