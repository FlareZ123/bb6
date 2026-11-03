import Lean.Elab.Tactic.Omega

namespace BB6ChampionArithmetic

/-- Powers of two alternate between 1 and 2 modulo three. -/
theorem pow2_even_mod3 (k : Nat) : (2 ^ (2 * k)) % 3 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have e : 2 * (k+1) = 2*k+2 := by omega
    rw [e, Nat.pow_add]
    simp [Nat.mul_mod, ih]

theorem pow2_odd_mod3 (k : Nat) : (2 ^ (2*k+1)) % 3 = 2 := by
  rw [Nat.pow_add, Nat.mul_mod, pow2_even_mod3]

/-- The index created by the published TM63 Rst1' macro. -/
def resetIndex (length exponent : Nat) : Nat :=
  (4 * 2^length - 1) * 2^exponent - 1

private theorem pow2_pos (n : Nat) : 0 < 2^n := Nat.pow_pos (by decide)

private theorem base_even_mod3 (k : Nat) : (4 * 2^(2*k) - 1) % 3 = 0 := by
  have hh : (4 * 2^(2*k)) % 3 = 1 := by
    rw [Nat.mul_mod, pow2_even_mod3]
  omega

private theorem base_odd_mod3 (k : Nat) : (4 * 2^(2*k+1) - 1) % 3 = 1 := by
  have hh : (4 * 2^(2*k+1)) % 3 = 2 := by
    rw [Nat.mul_mod, pow2_odd_mod3]
  omega

private theorem base_pos (n : Nat) : 0 < 4 * 2^n - 1 := by
  have hp := pow2_pos n
  omega

private theorem reset_of_base_zero (base exponent : Nat)
    (h : base % 3 = 0) (hp : 0 < base) :
    (base * 2^exponent - 1) % 3 = 2 := by
  have d : 3 ∣ base := Nat.dvd_of_mod_eq_zero h
  rcases d with ⟨j,hj⟩
  have jp : 0 < j := by omega
  have p := pow2_pos exponent
  have jpos : 0 < j*2^exponent := Nat.mul_pos jp p
  have eq : base * 2^exponent - 1 = 3*(j*2^exponent-1)+2 := by
    rw [hj]
    rw [Nat.mul_assoc]
    omega
  rw [eq]
  omega

private theorem reset_of_base_one_even (base k : Nat)
    (h : base % 3 = 1) :
    (base * 2^(2*k) - 1) % 3 = 0 := by
  have hh : (base * 2^(2*k)) % 3 = 1 := by
    rw [Nat.mul_mod, h, pow2_even_mod3]
  omega

private theorem reset_of_base_one_odd (base k : Nat)
    (h : base % 3 = 1) :
    (base * 2^(2*k+1) - 1) % 3 = 1 := by
  have hh : (base * 2^(2*k+1)) % 3 = 2 := by
    rw [Nat.mul_mod, h, pow2_odd_mod3]
  omega

/-- Even-length middle-one resets enter the terminal modulo-three class. -/
theorem even_length_reset (k a : Nat) : resetIndex (2*k) a % 3 = 2 := by
  exact reset_of_base_zero _ _ (base_even_mod3 k) (base_pos _)

/-- The two other parameter parity sectors have residues zero and one. -/
theorem odd_length_even_exponent_reset (k a : Nat) :
    resetIndex (2*k+1) (2*a) % 3 = 0 := by
  exact reset_of_base_one_even _ a (base_odd_mod3 k)

theorem odd_length_odd_exponent_reset (k a : Nat) :
    resetIndex (2*k+1) (2*a+1) % 3 = 1 := by
  exact reset_of_base_one_odd _ a (base_odd_mod3 k)

/-- The next reset from odd length and odd exponent has even length. -/
theorem odd_odd_next_length (k a : Nat) :
    (2*k+1) + 2 + (2*a+1) = 2*(k+a+2) := by omega

/-- The published nested recurrences from BusyCoq TM63. -/
def tower : Nat → Nat → Nat
  | 0, b => b
  | n+1, b => 2^(tower n b)-1

def sumTower : Nat → Nat → Nat
  | 0, b => b
  | n+1, b => sumTower n b + tower (n+1) b

private theorem tower_positive (n b : Nat) (hb : 0 < b) : 0 < tower n b := by
  induction n with
  | zero => simpa [tower] using hb
  | succ n ih =>
    simp only [tower]
    obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ih)
    rw [hj, Nat.pow_succ]
    have hpow := pow2_pos j
    omega

theorem tower_succ_odd (n b : Nat) (hb : 0 < b) :
    tower (n+1) b % 2 = 1 := by
  simp only [tower]
  have hp := tower_positive n b hb
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
  rw [hj, Nat.pow_succ]
  have hpow := pow2_pos j
  have hmul : (2^j * 2) % 2 = 0 := by omega
  omega

theorem sumTower_parity (n b : Nat) (hb : 0 < b) :
    sumTower n b % 2 = (b+n) % 2 := by
  induction n with
  | zero => simp [sumTower]
  | succ n ih =>
    change (sumTower n b + tower (n+1) b) % 2 = (b+(n+1)) % 2
    rw [Nat.add_mod, ih, tower_succ_odd n b hb]
    omega

/-- The intermediate exponent after the first seven decrements is odd. -/
theorem initial_reset_exponent_odd : (sumTower 7 6 + 12) % 2 = 1 := by
  have h := sumTower_parity 7 6 (by decide)
  omega

theorem odd_odd_two_stage_gate (k a exponent : Nat) :
    resetIndex (2*k+1) (2*a+1) % 3 = 1 ∧
    resetIndex ((2*k+1)+2+(2*a+1)) exponent % 3 = 2 := by
  constructor
  · exact odd_length_odd_exponent_reset k a
  · rw [odd_odd_next_length]
    exact even_length_reset (k+a+2) exponent

theorem reset_of_odd_exponent (a exponent : Nat) (ha : a % 2 = 1) :
    resetIndex 3 a % 3 = 1 ∧
    resetIndex (3+2+a) exponent % 3 = 2 := by
  have he : a = 2*(a/2)+1 := by omega
  rw [he]
  exact odd_odd_two_stage_gate 1 (a/2) exponent

/-- Published genuine TM63 entry (L=3,n=7,b=6), with huge exponent symbolic. -/
theorem published_blank_gate_general (exponent : Nat) :
    resetIndex 3 (sumTower 7 6 + 12) % 3 = 1 ∧
    resetIndex (3+2+(sumTower 7 6 + 12)) exponent % 3 = 2 :=
  reset_of_odd_exponent (sumTower 7 6 + 12) exponent initial_reset_exponent_odd

theorem published_blank_gate :
    resetIndex 3 (sumTower 7 6 + 12) % 3 = 1 ∧
    resetIndex (3+2+(sumTower 7 6 + 12)) (tower 8 6) % 3 = 2 :=
  published_blank_gate_general (tower 8 6)

#print axioms even_length_reset
#print axioms odd_length_even_exponent_reset
#print axioms odd_length_odd_exponent_reset
#print axioms tower_succ_odd
#print axioms sumTower_parity
#print axioms odd_odd_two_stage_gate
#print axioms published_blank_gate

end BB6ChampionArithmetic
