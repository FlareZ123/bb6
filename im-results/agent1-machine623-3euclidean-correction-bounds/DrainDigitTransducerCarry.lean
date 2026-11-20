import Lean

/-!
# Three-state ternary drain transducer

The states carry the exact quotient in the low-digit identity
  4 * outputPrefix - 2 * inputPrefix + carry(state)
    = 3^n * carry(finalState).
The transition table is the minimal three-state quotient used in the
#623 drain-correction note.
-/

inductive DrainState where
  | A | B | C
  deriving DecidableEq, Repr

open DrainState

def carry : DrainState → Int
  | A => 1
  | B => 3
  | C => -1

def step (s : DrainState) (d : Nat) : DrainState × Int :=
  match s, d with
  | A, 0 => (B, 2)
  | A, 1 => (A, 1)
  | A, 2 => (C, 0)
  | B, 0 => (A, 0)
  | B, 1 => (B, 2)
  | B, 2 => (A, 1)
  | C, 0 => (A, 1)
  | C, 1 => (C, 0)
  | C, 2 => (A, 2)
  | _, _ => (A, 0)

/-- One-step carry identity for each of the nine transitions. -/
theorem step_carry (s : DrainState) (d : Nat) (hd : d < 3) :
    3 * carry (step s d).1 =
      carry s + 4 * (step s d).2 - 2 * Int.ofNat d := by
  cases s with
  | A =>
    cases d with
    | zero => simp [step, carry]
    | succ d =>
      cases d with
      | zero => simp [step, carry]
      | succ d =>
        cases d with
        | zero => simp [step, carry]
        | succ d => omega
  | B =>
    cases d with
    | zero => simp [step, carry]
    | succ d =>
      cases d with
      | zero => simp [step, carry]
      | succ d =>
        cases d with
        | zero => simp [step, carry]
        | succ d => omega
  | C =>
    cases d with
    | zero => simp [step, carry]
    | succ d =>
      cases d with
      | zero => simp [step, carry]
      | succ d =>
        cases d with
        | zero => simp [step, carry]
        | succ d => omega

def lowDigits : Nat → Nat → Int
  | 0, _ => 0
  | n + 1, b => Int.ofNat (b % 3) + 3 * lowDigits n (b / 3)

def pow3 : Nat → Int
  | 0 => 1
  | n + 1 => 3 * pow3 n

def run : Nat → Nat → DrainState → Int × DrainState
  | 0, _, s => (0, s)
  | n + 1, b, s =>
      let (s', out) := step s (b % 3)
      let (tail, finalState) := run n (b / 3) s'
      (out + 3 * tail, finalState)

/-- The exact carry invariant, for every input word and every initial state. -/
theorem run_carry (n b : Nat) (s : DrainState) :
    4 * (run n b s).1 - 2 * lowDigits n b + carry s
      = pow3 n * carry (run n b s).2 := by
  induction n generalizing b s with
  | zero => simp [run, lowDigits, pow3]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
        have hd : b % 3 < 3 := Nat.mod_lt _ (by decide)
        have hstep := step_carry s (b % 3) hd
        have htail := ih (b / 3) s'
        simp [hst] at hstep
        simp only [run, lowDigits, hst] at ⊢
        have htail3 := congrArg (fun z : Int => 3 * z) htail
        simp [Int.mul_add, Int.mul_assoc, pow3] at htail3 ⊢
        omega

def phaseBit : DrainState → Nat
  | A => 0
  | B => 1
  | C => 1

theorem step_phase (s : DrainState) (d : Nat) (hd : d < 3) :
    phaseBit (step s d).1 = (phaseBit s + (if d = 1 then 0 else 1)) % 2 := by
  cases s with
  | A =>
    cases d with
    | zero => simp [step, phaseBit]
    | succ d =>
      cases d with
      | zero => simp [step, phaseBit]
      | succ d =>
        cases d with
        | zero => simp [step, phaseBit]
        | succ d => omega
  | B =>
    cases d with
    | zero => simp [step, phaseBit]
    | succ d =>
      cases d with
      | zero => simp [step, phaseBit]
      | succ d =>
        cases d with
        | zero => simp [step, phaseBit]
        | succ d => omega
  | C =>
    cases d with
    | zero => simp [step, phaseBit]
    | succ d =>
      cases d with
      | zero => simp [step, phaseBit]
      | succ d =>
        cases d with
        | zero => simp [step, phaseBit]
        | succ d => omega

theorem run_phase (n b : Nat) (s : DrainState) (hb : b < 3 ^ n) :
    phaseBit (run n b s).2 = (phaseBit s + n + b) % 2 := by
  induction n generalizing b s with
  | zero =>
      have hb0 : b = 0 := by omega
      subst b
      cases s <;> simp [run, phaseBit]
  | succ n ih =>
      have hdiv : b / 3 < 3 ^ n := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).2
        simpa [Nat.pow_succ, Nat.mul_comm] using hb
      cases hst : step s (b % 3) with
      | mk s' out =>
        have hd : b % 3 < 3 := Nat.mod_lt _ (by decide)
        have hphase := step_phase s (b % 3) hd
        have htail := ih (b / 3) s' hdiv
        have hmod := Nat.mod_add_div b 3
        have hdCases : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
        simp [hst] at hphase
        simp only [run, hst]
        rcases hdCases with h0 | h1 | h2
        · simp [h0] at hphase
          rw [htail, hphase]
          rw [h0] at hmod
          omega
        · simp [h1] at hphase
          rw [htail, hphase]
          rw [h1] at hmod
          omega
        · simp [h2] at hphase
          rw [htail, hphase]
          rw [h2] at hmod
          omega

theorem lowDigits_eq_of_lt (n b : Nat) (hb : b < 3 ^ n) :
    lowDigits n b = Int.ofNat b := by
  induction n generalizing b with
  | zero =>
      have hb0 : b = 0 := by omega
      subst b
      simp [lowDigits]
  | succ n ih =>
      have hdiv : b / 3 < 3 ^ n := by
        apply (Nat.div_lt_iff_lt_mul (by decide)).2
        simpa [Nat.pow_succ, Nat.mul_comm] using hb
      have htail := ih (b / 3) hdiv
      rw [lowDigits, htail]
      have hmod := Nat.mod_add_div b 3
      have hcast := congrArg Int.ofNat hmod
      simpa [Int.natCast_add] using hcast

theorem pow3_eq_nat (n : Nat) : pow3 n = Int.ofNat (3 ^ n) := by
  induction n with
  | zero => simp [pow3]
  | succ n ih =>
      simp [pow3, Nat.pow_succ, ih, Int.mul_comm]

/-- Every emitted digit is nonnegative and at most two. -/
theorem step_output_bounds (s : DrainState) (d : Nat) :
    0 ≤ (step s d).2 ∧ (step s d).2 ≤ 2 := by
  cases s with
  | A =>
    cases d with
    | zero => simp [step]
    | succ d =>
      cases d with
      | zero => simp [step]
      | succ d =>
        cases d with
        | zero => simp [step]
        | succ d => simp [step]
  | B =>
    cases d with
    | zero => simp [step]
    | succ d =>
      cases d with
      | zero => simp [step]
      | succ d =>
        cases d with
        | zero => simp [step]
        | succ d => simp [step]
  | C =>
    cases d with
    | zero => simp [step]
    | succ d =>
      cases d with
      | zero => simp [step]
      | succ d =>
        cases d with
        | zero => simp [step]
        | succ d => simp [step]

/-- The emitted integer is nonnegative. -/
theorem run_nonneg (n b : Nat) (s : DrainState) :
    0 ≤ (run n b s).1 := by
  induction n generalizing b s with
  | zero => simp [run]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
        have hout := step_output_bounds s (b % 3)
        simp [hst] at hout
        have htail := ih (b / 3) s'
        simp only [run, hst]
        omega

/-- The emitted integer is strictly smaller than 3^n. -/
theorem run_lt_pow3 (n b : Nat) (s : DrainState) :
    (run n b s).1 < pow3 n := by
  induction n generalizing b s with
  | zero => simp [run, pow3]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
        have hout := step_output_bounds s (b % 3)
        simp [hst] at hout
        have htail := ih (b / 3) s'
        simp only [run, hst, pow3]
        omega

theorem pow3_odd (n : Nat) : 3 ^ n % 2 = 1 := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.pow_succ, Nat.mul_mod, ih]

/--
The three-state transducer computes the exact integer
  N = (2 b - 1 + 3^L) / 4
whenever L has the parity of b and the defining upper size bound holds.
The input low is the low-L-digit part of b and high is its (0 or 1)
leading ternary digit.
-/
theorem drain_transducer_exact (L low high : Nat)
    (hlow : low < 3 ^ L) (hhigh : high ≤ 1)
    (hpar : L % 2 = (low + high * 3 ^ L) % 2)
    (hsize : 2 * Int.ofNat (low + high * 3 ^ L) - 1 < pow3 (L + 1)) :
    4 * (run L low A).1 =
      2 * Int.ofNat (low + high * 3 ^ L) - 1 + pow3 L := by
  have hcarry := run_carry L low A
  rw [lowDigits_eq_of_lt L low hlow] at hcarry
  have hphase := run_phase L low A hlow
  simp [phaseBit] at hphase
  have hnonneg := run_nonneg L low A
  have hhighCases : high = 0 ∨ high = 1 := by omega
  rcases hhighCases with hzero | hone
  · subst high
    have hpar0 : L % 2 = low % 2 := by simpa using hpar
    have hphase0 : (L + low) % 2 = 0 := by omega
    rw [hphase0] at hphase
    have hfinal : (run L low A).2 = A := by
      cases h : (run L low A).2 <;> simp [h] at hphase ⊢
    simp [hfinal, carry] at hcarry ⊢
    omega
  · subst high
    have hodd := pow3_odd L
    have hpar1 : L % 2 = (low + 3 ^ L) % 2 := by simpa using hpar
    have hphase1 : (L + low) % 2 = 1 := by omega
    rw [hphase1] at hphase
    cases hfinal : (run L low A).2 with
    | A => simp [hfinal] at hphase
    | B =>
        simp [hfinal, carry, pow3_eq_nat, Int.natCast_add] at hcarry ⊢
        omega
    | C =>
        simp [hfinal, carry, pow3_eq_nat, Int.natCast_add] at hcarry hsize ⊢
        omega
