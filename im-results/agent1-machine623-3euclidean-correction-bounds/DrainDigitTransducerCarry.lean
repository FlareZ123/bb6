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


theorem pow3_pos (n : Nat) : 0 < pow3 n := by
  induction n with
  | zero => simp [pow3]
  | succ n ih => simp [pow3]; omega

/-- Exact formula directly from the length parity and upper-size conditions. -/
theorem drain_transducer_exact_of_bounds (L b : Nat)
    (hpar : L % 2 = b % 2)
    (hsize : 2 * Int.ofNat b - 1 < pow3 (L + 1)) :
    4 * (run L (b % 3 ^ L) A).1 =
      2 * Int.ofNat b - 1 + pow3 L := by
  have hpow : 0 < pow3 L := pow3_pos L
  have hpowSucc : pow3 (L + 1) = 3 * pow3 L := by simp [pow3]
  have hsize' : 2 * Int.ofNat b < 3 * pow3 L + 1 := by
    rw [hpowSucc] at hsize
    omega
  have hlt : Int.ofNat b < 2 * pow3 L := by omega
  have hNat : b < 2 * 3 ^ L := by
    apply Int.ofNat_lt.mp
    simpa [pow3_eq_nat] using hlt
  have hk : 0 < 3 ^ L := Nat.pow_pos (by decide)
  have hdiv : b / 3 ^ L < 2 :=
    (Nat.div_lt_iff_lt_mul hk).2 (by simpa [Nat.mul_comm] using hNat)
  have hhigh : b / 3 ^ L ≤ 1 := by omega
  let low := b % 3 ^ L
  let high := b / 3 ^ L
  have hlow : low < 3 ^ L := by
    dsimp [low]
    exact Nat.mod_lt _ hk
  have hdecomp : low + high * 3 ^ L = b := by
    dsimp [low, high]
    simpa [Nat.mul_comm] using Nat.mod_add_div b (3 ^ L)
  have hpar' : L % 2 = (low + high * 3 ^ L) % 2 := by
    rw [hdecomp]
    exact hpar
  have hsize'' : 2 * Int.ofNat (low + high * 3 ^ L) - 1 < pow3 (L + 1) := by
    rw [hdecomp]
    exact hsize
  have hExact := drain_transducer_exact L low high hlow hhigh hpar' hsize''
  rw [hdecomp] at hExact
  exact hExact


structure DrainStats where
  output : Int
  ones : Nat
  twos : Nat
  finalState : DrainState
  deriving Repr

/-- Run the transducer while retaining the counts of output digits 1 and 2. -/
def runStats : Nat → Nat → DrainState → DrainStats
  | 0, _, s => ⟨0, 0, 0, s⟩
  | n + 1, b, s =>
      let (s', out) := step s (b % 3)
      let tail := runStats n (b / 3) s'
      ⟨out + 3 * tail.output,
       tail.ones + (if out = 1 then 1 else 0),
       tail.twos + (if out = 2 then 1 else 0),
       tail.finalState⟩

theorem runStats_output_eq (n b : Nat) (s : DrainState) :
    (runStats n b s).output = (run n b s).1 := by
  induction n generalizing b s with
  | zero => simp [runStats, run]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
        simp [runStats, run, hst, ih]

/-- At most one nonzero output digit is counted at each transducer step. -/
theorem runStats_count_bounds (n b : Nat) (s : DrainState) :
    (runStats n b s).twos ≤ (runStats n b s).ones + (runStats n b s).twos ∧
    (runStats n b s).ones + (runStats n b s).twos ≤ n := by
  induction n generalizing b s with
  | zero => simp [runStats]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
        have hout := step_output_bounds s (b % 3)
        simp [hst] at hout
        have htail := ih (b / 3) s'
        simp only [runStats, hst]
        have hdigit : (if out = 1 then 1 else 0) + (if out = 2 then 1 else 0) ≤ 1 := by
          by_cases h1 : out = 1 <;> by_cases h2 : out = 2 <;> simp [h1, h2] at * <;> omega
        constructor
        · omega
        · omega

/-- Exact output theorem with the weighted digit counts retained. -/
theorem runStats_exact_of_bounds (L b : Nat)
    (hpar : L % 2 = b % 2)
    (hsize : 2 * Int.ofNat b - 1 < pow3 (L + 1)) :
    4 * (runStats L (b % 3 ^ L) A).output =
      2 * Int.ofNat b - 1 + pow3 L := by
  simpa [runStats_output_eq] using drain_transducer_exact_of_bounds L b hpar hsize


/-- Canonical-ray specialization: the lower inequality records the chosen digit length. -/
theorem drain_transducer_exact_canonical (L b : Nat)
    (hpar : L % 2 = b % 2)
    (hlo : 3 ^ (L - 1) ≤ 2 * b - 1)
    (hhi : 2 * b - 1 < 3 ^ (L + 1)) :
    4 * (runStats L (b % 3 ^ L) A).output =
      2 * Int.ofNat b - 1 + pow3 L := by
  have hpowLo : 0 < 3 ^ (L - 1) := Nat.pow_pos (by decide)
  have hb1 : 1 ≤ 2 * b := by omega
  have hsub : Int.ofNat (2 * b - 1) = 2 * Int.ofNat b - 1 := by
    calc
      Int.ofNat (2 * b - 1) = Int.ofNat (2 * b) - Int.ofNat 1 := Int.ofNat_sub hb1
      _ = 2 * Int.ofNat b - 1 := by simp [Int.natCast_mul]
  have hhiCast : Int.ofNat (2 * b - 1) < Int.ofNat (3 ^ (L + 1)) :=
    Int.ofNat_lt.mpr hhi
  have hhiInt : 2 * Int.ofNat b - 1 < pow3 (L + 1) := by
    rw [pow3_eq_nat, ← hsub]
    exact hhiCast
  exact runStats_exact_of_bounds L b hpar hhiInt


theorem runStats_finalState_eq (n b : Nat) (s : DrainState) :
    (runStats n b s).finalState = (run n b s).2 := by
  induction n generalizing b s with
  | zero => simp [runStats, run]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out => simp [runStats, run, hst, ih]

/-- The terminal transducer phase is exactly the leading ternary digit high. -/
theorem runStats_phase_of_decomposition (L low high : Nat)
    (hlow : low < 3 ^ L) (hhigh : high ≤ 1)
    (hpar : L % 2 = (low + high * 3 ^ L) % 2) :
    phaseBit (runStats L low A).finalState = high := by
  have hphase := run_phase L low A hlow
  simp [phaseBit] at hphase
  rw [runStats_finalState_eq]
  have hodd := pow3_odd L
  have hphase' : (L + low) % 2 = high := by
    by_cases hzero : high = 0
    · subst high
      simp at hpar
      omega
    · have hone : high = 1 := by omega
      subst high
      omega
  rw [hphase'] at hphase
  exact hphase


def weightedE (stats : DrainStats) : Int := Int.ofNat stats.twos
def weightedR (stats : DrainStats) : Int := Int.ofNat (stats.ones + stats.twos)
def weightedD (L : Nat) (stats : DrainStats) : Int := Int.ofNat L - 2 * weightedE stats

/-- The weighted statistics satisfy the exact hypotheses used by the correction bounds. -/
theorem runStats_weight_bounds (L b : Nat) (s : DrainState) :
    0 ≤ weightedE (runStats L b s) ∧
    weightedE (runStats L b s) ≤ weightedR (runStats L b s) ∧
    weightedR (runStats L b s) ≤ Int.ofNat L := by
  have h := runStats_count_bounds L b s
  simp [weightedE, weightedR] at ⊢
  omega

/-! ## Nine-state product: drain state × nonzero-output count modulo 3

The second register counts emitted digits 1 and 2 modulo 3.  Since the
underlying drain transducer has three states, this is a nine-state
deterministic product.  It is the exact finite memory needed for the
passive-register low-digit update in the #623 two-coordinate cocycle.
-/

def nonzeroOutputWeight (out : Int) : Nat := if out = 0 then 0 else 1

def drainNineStep (s : DrainState × Nat) (d : Nat) : DrainState × Nat :=
  let (s', out) := step s.1 d
  (s', (s.2 + nonzeroOutputWeight out) % 3)

def drainNineRun : Nat → Nat → DrainState × Nat → DrainState × Nat
  | 0, _, (s, rho) => (s, rho % 3)
  | n + 1, b, s => drainNineRun n (b / 3) (drainNineStep s (b % 3))

theorem nonzeroOutputWeight_eq_count (out : Int)
    (hout : 0 ≤ out ∧ out ≤ 2) :
    nonzeroOutputWeight out =
      (if out = 1 then 1 else 0) + (if out = 2 then 1 else 0) := by
  unfold nonzeroOutputWeight
  by_cases h0 : out = 0
  · simp [h0]
  · have h12 : out = 1 ∨ out = 2 := by omega
    rcases h12 with h1 | h2 <;> simp [h0, h1, h2]

theorem drainNineRun_count (n b : Nat) (s : DrainState) (rho : Nat) :
    (drainNineRun n b (s, rho)).2 =
      (rho + (runStats n b s).ones + (runStats n b s).twos) % 3 := by
  induction n generalizing b s rho with
  | zero => simp [drainNineRun, runStats]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
          have hout := step_output_bounds s (b % 3)
          simp [hst] at hout
          have hinc := nonzeroOutputWeight_eq_count out hout
          have htail := ih (b / 3) s' ((rho + nonzeroOutputWeight out) % 3)
          simp only [drainNineRun, drainNineStep, hst]
          rw [htail]
          simp only [runStats, hst]
          rw [hinc]
          omega

theorem drainNineRun_finalState (n b : Nat) (s : DrainState) (rho : Nat) :
    (drainNineRun n b (s, rho)).1 = (run n b s).2 := by
  induction n generalizing b s rho with
  | zero => simp [drainNineRun, run]
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
          have htail := ih (b / 3) s' ((rho + nonzeroOutputWeight out) % 3)
          simp [drainNineRun, drainNineStep, run, hst, htail]

theorem drainNineRun_phase_lt_three (n b : Nat) (s : DrainState) (rho : Nat)
    (hrho : rho < 3) : (drainNineRun n b (s, rho)).2 < 3 := by
  induction n generalizing b s rho with
  | zero => simpa [drainNineRun] using hrho
  | succ n ih =>
      cases hst : step s (b % 3) with
      | mk s' out =>
          apply ih
          simp [drainNineStep, hst]

theorem drainNineRun_count_mod3 (n b : Nat) (s : DrainState) :
    (drainNineRun n b (s, 0)).2 =
      ((runStats n b s).ones + (runStats n b s).twos) % 3 := by
  simpa using drainNineRun_count n b s 0

#print axioms drainNineRun_count
#print axioms drainNineRun_finalState
