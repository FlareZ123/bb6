import Lean

/-!
# Isolated Lean model of the SectionResult q4 cost identity

The definitions 'v2', 'proposedIncrementCost', 'nextMarker',
'nextExponent', 'nextRight', 'SectionResult', and 'sectionResult' below
are copied from 'im-results/agent24-champion-time/CostRecurrence.lean'
into a fresh namespace so this file can be checked without the repository's
full import closure. The theorems are machine-checked facts about this
source-shaped recurrence model, including the one-dimensional cost form. They are **not** a compilation of the
original source module, a proof that the candidate cost equals a TM2 run
length, or an accepted blank-root halt/score theorem.

Checked with Lean 4.36.0-rc2. The '#print axioms' lines at the end expose
the dependencies of the principal results.
-/

namespace BB6SectionResultModel

/-- The same v₂ convention and recurrence used by CostRecurrence.lean. -/
def v2 (n : Nat) : Nat :=
  if h : n ≤ 1 then 0
  else if n % 2 = 0 then 1 + v2 (n / 2) else 0
termination_by n
decreasing_by omega

/-- Binary digit sum, defined by the usual quotient/remainder recursion. -/
def popCount : Nat → Nat
  | 0 => 0
  | n+1 => popCount ((n+1)/2) + (n+1)%2
termination_by n => n
decreasing_by omega

theorem popCount_two_mul (n : Nat) : popCount (2*n) = popCount n := by
  cases n with
  | zero => rfl
  | succ n =>
    have hdiv : (2*(n+1))/2 = n+1 := by omega
    have hmod : (2*(n+1))%2 = 0 := by omega
    have hEq : 2*(n+1) = (2*(n+1)-1)+1 := by omega
    have hdiv' : (2*(n+1)-1+1)/2 = n+1 := by omega
    have hmod' : (2*(n+1)-1+1)%2 = 0 := by omega
    rw [hEq, popCount.eq_2, hdiv', hmod']
    omega

theorem popCount_two_mul_add_one (n : Nat) : popCount (2*n+1) = popCount n + 1 := by
  have hdiv : (2*n+1)/2 = n := by omega
  have hmod : (2*n+1)%2 = 1 := by omega
  rw [popCount.eq_2, hdiv, hmod]

theorem v2_two_mul (n : Nat) (hn : 0 < n) : v2 (2*n) = 1 + v2 n := by
  have hnot : ¬ 2*n ≤ 1 := by omega
  have hmod : (2*n)%2 = 0 := by omega
  have hdiv : (2*n)/2 = n := by omega
  rw [v2.eq_1]
  simp [hnot, hmod, hdiv]

theorem v2_two_mul_add_one (n : Nat) : v2 (2*n+1) = 0 := by
  rw [v2.eq_1]
  by_cases h : 2*n+1 ≤ 1
  · have hn : n = 0 := by omega
    subst n
    simp
  · have hmod : (2*n+1)%2 ≠ 0 := by omega
    simp [h]

/-- Binary increment: adding one flips all trailing ones to zero and
adds one new leading bit; the number of flipped bits is v₂(n+1). -/
theorem popCount_succ_add_v2 (n : Nat) :
    popCount (n+1) + v2 (n+1) = popCount n + 1 := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases he : (n+1)%2 = 0
    · let k := (n+1)/2
      have hk : 0 < k := by dsimp [k]; omega
      have hdecomp : n+1 = 2*k := by dsimp [k]; omega
      have hprev : n = 2*(k-1)+1 := by dsimp [k]; omega
      have hsmall : k-1 < n := by omega
      have hrec := ih (k-1) hsmall
      have hkm1 : (k-1)+1 = k := by omega
      have hrec' : popCount k + v2 k = popCount (k-1) + 1 := by
        simpa [hkm1] using hrec
      rw [hdecomp, hprev, popCount_two_mul, popCount_two_mul_add_one,
        v2_two_mul k hk]
      omega
    · let k := (n+1)/2
      have hdecomp : n+1 = 2*k+1 := by dsimp [k]; omega
      have hprev : n = 2*k := by dsimp [k]; omega
      rw [hdecomp, hprev, popCount_two_mul_add_one, popCount_two_mul,
        v2_two_mul_add_one]

def sumV2 : Nat → Nat
  | 0 => 0
  | n+1 => sumV2 n + v2 (n+1)

theorem sumV2_add_popCount (n : Nat) : sumV2 n + popCount n = n := by
  induction n with
  | zero => simp [sumV2, popCount]
  | succ n ih =>
    simp only [sumV2]
    have h := popCount_succ_add_v2 n
    omega

/-- The exact one-stage candidate cost from CostRecurrence.lean. -/
def proposedIncrementCost (m n a b : Nat) : Nat :=
  6*4^b + 42*2^b + 15 + 4*m + 12*(a+v2 n) - 9*b

def nextMarker (m : Nat) : Nat := (m+2)%3
def nextExponent (m a b : Nat) : Nat := a+b+(if m%3=0 then 1 else 2)
def nextRight (b : Nat) : Nat := 2^b-1

structure SectionResult where
  marker : Nat
  exponent : Nat
  right : Nat
  cost : Nat
  deriving Repr

def sectionResult : Nat → Nat → Nat → Nat → SectionResult
  | 0, m, a, b => ⟨m%3, a, b, 0⟩
  | n+1, m, a, b =>
    let m' := nextMarker m
    let a' := nextExponent m a b
    let b' := nextRight b
    let rest := sectionResult n m' a' b'
    { rest with cost := proposedIncrementCost (m%3) (n+1) a b + rest.cost }

/-- The non-valuation part of a stage's candidate cost. -/
def rawTerm (a b : Nat) : Nat := 6*4^b + 42*2^b + 12*a - 9*b

def rawSum : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | n+1, m, a, b =>
      rawTerm a b + rawSum n (nextMarker m) (nextExponent m a b) (nextRight b)

def markerSum : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, m => m%3 + markerSum n (nextMarker m)

private theorem nat_le_two_pow (b : Nat) : b ≤ 2^b := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hp : 0 < 2^b := Nat.pow_pos (by decide)
    calc
      b+1 ≤ 2^b+1 := Nat.succ_le_succ ih
      _ ≤ 2^b+2^b := by omega
      _ = 2^(b+1) := by simp [Nat.pow_succ, Nat.mul_two]

theorem proposedIncrementCost_eq_raw (m n a b : Nat) :
    proposedIncrementCost m n a b =
      rawTerm a b + 15 + 4*m + 12*v2 n := by
  have hb : b ≤ 2^b := nat_le_two_pow b
  have hsub : 9*b ≤ 6*4^b + 42*2^b + 12*a := by omega
  unfold proposedIncrementCost rawTerm
  have hbase : 9*b ≤ 6*4^b + 42*2^b + 12*a := hsub
  omega

theorem sectionResult_cost_decomposition (n m a b : Nat) :
    (sectionResult n m a b).cost =
      rawSum n m a b + 15*n + 4*markerSum n m + 12*sumV2 n := by
  induction n generalizing m a b with
  | zero => rfl
  | succ n ih =>
    simp only [sectionResult, rawSum, markerSum, sumV2]
    rw [ih]
    rw [proposedIncrementCost_eq_raw]
    omega

theorem markerSum_three_cycle (k : Nat) : markerSum (3*k) 0 = 3*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : markerSum (3*k+3) 0 = 3 + markerSum (3*k) 0 := by
      simp [markerSum, nextMarker] <;> omega
    calc
      markerSum (3*(k+1)) 0 = markerSum (3*k+3) 0 := by congr 1 <;> omega
      _ = 3 + markerSum (3*k) 0 := hstep
      _ = 3*(k+1) := by omega

/-- Exact candidate cost for a marker-zero dispatcher whose length is
multiple of three. The only nontrivial correction is the binary digit sum. -/
theorem sectionResult_cost_three_cycle (k a b : Nat) :
    (sectionResult (3*k) 0 a b).cost =
      31*(3*k) - 12*popCount (3*k) + rawSum (3*k) 0 a b := by
  have hdecomp := sectionResult_cost_decomposition (3*k) 0 a b
  have hmark := markerSum_three_cycle k
  have hval := sumV2_add_popCount (3*k)
  omega


/-- The marker-dependent additive increment in the exponent recurrence. -/
def epsilon (m : Nat) : Nat := if m%3=0 then 1 else 2

def weightedEpsilonSum : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, m => (n+1)*epsilon m + weightedEpsilonSum n (nextMarker m)

/-- The one-dimensional right-counter sum, with coefficient determined by
how many increments remain at the current stage. -/
def oneDimSum : Nat → Nat → Nat
  | 0, _ => 0
  | n+1, b =>
      6*4^b + 42*2^b + (12*(n+1)-9)*b + oneDimSum n (nextRight b)

/-- Exact elimination of the intermediate exponent sequence, valid for
any initial marker and any dispatcher length. -/
theorem rawSum_add_terminalExponent (n m a b : Nat) :
    rawSum n m a b + 12*(sectionResult n m a b).exponent =
      12*(n+1)*a + oneDimSum n b + 12*weightedEpsilonSum n m := by
  induction n generalizing m a b with
  | zero => simp [rawSum, sectionResult, oneDimSum, weightedEpsilonSum]
  | succ n ih =>
    simp only [rawSum, oneDimSum, weightedEpsilonSum, sectionResult]
    rw [Nat.add_assoc, ih (nextMarker m) (nextExponent m a b) (nextRight b)]
    unfold rawTerm nextExponent epsilon
    have hcoeff : 9 ≤ 12*(n+1) := by omega
    have hbPow : b ≤ 2^b := nat_le_two_pow b
    have hrawSub : 9*b ≤ 6*4^b + 42*2^b + 12*a := by omega
    have hprod : 12*(n+1)*(a+b+(if m%3=0 then 1 else 2)) =
        12*(n+1)*a + 12*(n+1)*b + 12*(n+1)*(if m%3=0 then 1 else 2) := by
      simp [Nat.mul_add, Nat.add_assoc]
    have hfactor : 12*(n+1+1)*a = 12*(n+1)*a + 12*a := by
      calc
        12*(n+1+1)*a = (12*(n+1)+12)*a := by congr 2 <;> omega
        _ = 12*(n+1)*a + 12*a := by rw [Nat.add_mul]
    have hcoeffEq : 12*(n+1)=12*n+12 := by omega
    rw [hcoeffEq] at hprod hfactor
    rw [hcoeffEq]
    rw [hprod, hfactor]
    have hepsCoeff : (12*n+12)*(if m%3=0 then 1 else 2) =
        12*((n+1)*(if m%3=0 then 1 else 2)) := by
      calc
        (12*n+12)*(if m%3=0 then 1 else 2) =
            (12*(n+1))*(if m%3=0 then 1 else 2) := by congr 1 <;> omega
        _ = 12*((n+1)*(if m%3=0 then 1 else 2)) := by rw [Nat.mul_assoc]
    have hcoeffBase : 9 ≤ 12*n+12 := by omega
    have hbCoeff : (12*n+12)*b = (12*n+12-9)*b+9*b := by
      have hle : 9*b ≤ (12*n+12)*b := Nat.mul_le_mul_right b hcoeffBase
      calc
        (12*n+12)*b = ((12*n+12)*b-9*b)+9*b := (Nat.sub_add_cancel hle).symm
        _ = (12*n+12-9)*b+9*b := by rw [← Nat.sub_mul]
    rw [hepsCoeff, hbCoeff, Nat.mul_add]
    omega

/-- Weighted marker increments over each 0,2,1 cycle. -/
theorem weightedEpsilonSum_three_cycle (k : Nat) :
    2*weightedEpsilonSum (3*k) 0 = 15*k^2+3*k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hstep : weightedEpsilonSum (3*k+3) 0 =
        (3*k+3)*1 + (3*k+2)*2 + (3*k+1)*2 + weightedEpsilonSum (3*k) 0 := by
      simp [weightedEpsilonSum, epsilon, nextMarker] <;> omega
    have hsq : (k+1)^2 = k^2+2*k+1 := by
      simp [Nat.pow_succ, Nat.mul_add, Nat.mul_comm] <;> omega
    calc
      2*weightedEpsilonSum (3*(k+1)) 0 =
          2*weightedEpsilonSum (3*k+3) 0 := by congr 1 <;> omega
      _ = 2*((3*k+3)*1 + (3*k+2)*2 + (3*k+1)*2 +
          weightedEpsilonSum (3*k) 0) := by rw [hstep]
      _ = 2*((3*k+3)*1 + (3*k+2)*2 + (3*k+1)*2) +
          2*weightedEpsilonSum (3*k) 0 := by omega
      _ = 2*((3*k+3)*1 + (3*k+2)*2 + (3*k+1)*2) +
          (15*k^2+3*k) := by rw [ih]
      _ = 15*(k+1)^2+3*(k+1) := by rw [hsq]; omega

/-- One-dimensional exact form after adding the terminal 12E correction,
12W with W=popcount(N)+2, and the fixed 59+7 terminal/attainability cost.
The remaining sum depends only on the right-counter recurrence. -/
theorem sectionResult_one_dimensional_cost (k U R : Nat) :
    (sectionResult (3*k) 0 U R).cost +
      12*(sectionResult (3*k) 0 U R).exponent +
      12*(popCount (3*k)+2) + 66 =
    90*k^2 + 111*k + 90 + 12*(3*k+1)*U + oneDimSum (3*k) R := by
  have hcost := sectionResult_cost_three_cycle k U R
  have hraw := rawSum_add_terminalExponent (3*k) 0 U R
  have heps := weightedEpsilonSum_three_cycle k
  have hpop := sumV2_add_popCount (3*k)
  have hpopBound : popCount (3*k) ≤ 3*k := by omega
  have hle : 12*popCount (3*k) ≤ 31*(3*k) := by omega
  have heps' : 12*weightedEpsilonSum (3*k) 0 =
      6*(15*k^2+3*k) := by omega
  calc
    (sectionResult (3*k) 0 U R).cost +
        12*(sectionResult (3*k) 0 U R).exponent +
        12*(popCount (3*k)+2) + 66 =
      (31*(3*k)-12*popCount (3*k)+rawSum (3*k) 0 U R) +
        12*(sectionResult (3*k) 0 U R).exponent +
        12*(popCount (3*k)+2) + 66 := by rw [hcost]
    _ = 31*(3*k) +
        (rawSum (3*k) 0 U R + 12*(sectionResult (3*k) 0 U R).exponent) + 90 := by
      omega
    _ = 31*(3*k) +
        (12*(3*k+1)*U + oneDimSum (3*k) R +
          12*weightedEpsilonSum (3*k) 0) + 90 := by rw [hraw]
    _ = 90*k^2 + 111*k + 90 + 12*(3*k+1)*U + oneDimSum (3*k) R := by
      rw [heps']
      omega

/-- Powers of two have a single nonzero binary digit. -/
theorem popCount_pow_two_sub_one (n : Nat) : popCount (2^n-1) = n := by
  induction n with
  | zero => simp [popCount]
  | succ n ih =>
    have hpow : 2^(n+1) = 2^n*2 := by rw [Nat.pow_succ]
    have hform : 2^(n+1)-1 = 2*(2^n-1)+1 := by
      have hp : 0 < 2^n := Nat.pow_pos (by decide)
      rw [hpow]
      omega
    rw [hform, popCount_two_mul_add_one, ih]

/-- The binary expansion of 2^n-2 has n-1 one-bits for n>0. -/
theorem popCount_pow_two_sub_two (n : Nat) (hn : 0<n) :
    popCount (2^n-2) = n-1 := by
  have hpow : 2^n = 2^(n-1)*2 := by
    calc
      2^n = 2^((n-1)+1) := by congr 1 <;> omega
      _ = 2^(n-1)*2 := by rw [Nat.pow_succ]
  have hform : 2^n-2 = 2*(2^(n-1)-1) := by
    have hp : 0 < 2^(n-1) := Nat.pow_pos (by decide)
    rw [hpow]
    omega
  rw [hform, popCount_two_mul, popCount_pow_two_sub_one]

/-- Appending a low A-bit block to a shifted high block adds popcounts. -/
theorem popCount_shift_add (A x y : Nat) (hy : y < 2^A) :
    popCount (2^A*x+y) = popCount x + popCount y := by
  induction A generalizing x y with
  | zero =>
    have hy0 : y=0 := by simp at hy; omega
    subst y
    simp [popCount]
  | succ A ih =>
    have hpow : 2^(A+1)=2^A*2 := by rw [Nat.pow_succ]
    have hy' : y < 2^A*2 := by rw [← hpow]; exact hy
    have hdiv : y/2 < 2^A := by omega
    have hbit : y%2=0 ∨ y%2=1 := by omega
    rcases hbit with hzero | hone
    · have hyarg : y = 2*(y/2) := by omega
      have hmult : 2^(A+1)*x = 2*(2^A*x) := by
        calc
          2^(A+1)*x = (2^A*2)*x := by rw [hpow]
          _ = (2*2^A)*x := by rw [Nat.mul_comm (2^A) 2]
          _ = 2*(2^A*x) := by rw [Nat.mul_assoc]
      have harg : 2^(A+1)*x+y = 2*(2^A*x+y/2) := by
        rw [hmult, Nat.mul_add]
        omega
      have hpopY : popCount y = popCount (y/2) := by
        calc
          popCount y = popCount (2*(y/2)) := congrArg popCount hyarg
          _ = popCount (y/2) := popCount_two_mul (y/2)
      calc
        popCount (2^(A+1)*x+y) = popCount (2^A*x+y/2) := by rw [harg, popCount_two_mul]
        _ = popCount x + popCount (y/2) := ih x (y/2) hdiv
        _ = popCount x + popCount y := congrArg (fun t => popCount x + t) hpopY.symm
    · have hyarg : y = 2*(y/2)+1 := by omega
      have hmult : 2^(A+1)*x = 2*(2^A*x) := by
        calc
          2^(A+1)*x = (2^A*2)*x := by rw [hpow]
          _ = (2*2^A)*x := by rw [Nat.mul_comm (2^A) 2]
          _ = 2*(2^A*x) := by rw [Nat.mul_assoc]
      have harg : 2^(A+1)*x+y = 2*(2^A*x+y/2)+1 := by
        rw [hmult, Nat.mul_add]
        omega
      have hpopY : popCount y = popCount (y/2)+1 := by
        calc
          popCount y = popCount (2*(y/2)+1) := congrArg popCount hyarg
          _ = popCount (y/2)+1 := popCount_two_mul_add_one (y/2)
      calc
        popCount (2^(A+1)*x+y) = popCount (2^A*x+y/2)+1 := by rw [harg, popCount_two_mul_add_one]
        _ = popCount x + popCount (y/2)+1 := by rw [ih x (y/2) hdiv]
        _ = popCount x + popCount y := congrArg (fun t => popCount x + t) hpopY.symm

/-- Exact popcount of the arbitrary-A q4 terminal index. -/
theorem popCount_q4_terminal_index (A L : Nat) (hA : 2≤A) :
    popCount (2^A*(2^(L+2)-1)-3) = A+L := by
  have hpowA : 4≤2^A := by
    have h := Nat.pow_le_pow_right (by decide : 0<2) hA
    calc
      4 = 2^2 := by decide
      _ ≤ 2^A := h
  have hdecomp : 2^A*(2^(L+2)-1)-3 =
      2^A*(2^(L+2)-2)+(2^A-3) := by
    have hYbound : 2 ≤ 2^(L+2) := by
      have h := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤L+2)
      calc
        2 = 2^1 := by decide
        _ ≤ 2^2 := by decide
        _ ≤ 2^(L+2) := h
    have hY : 2^(L+2)-1 = (2^(L+2)-2)+1 := by omega
    rw [hY, Nat.mul_add]
    omega
  have hlow : 2^A-3 < 2^A := by omega
  have hshift := popCount_shift_add A (2^(L+2)-2) (2^A-3) hlow
  have hupperForm : 2^(L+2)-2 = 2*(2^(L+1)-1) := by
    have hpow : 2^(L+2)=2^(L+1)*2 := by rw [Nat.pow_succ]
    rw [hpow]
    omega
  have hupper : popCount (2^(L+2)-2) = L+1 := by
    rw [hupperForm, popCount_two_mul, popCount_pow_two_sub_one]
  have hlowerForm : 2^A-3 = 2*(2^(A-1)-2)+1 := by
    have hpow : 2^A=2^(A-1)*2 := by
      calc
        2^A = 2^((A-1)+1) := by congr 1 <;> omega
        _ = 2^(A-1)*2 := by rw [Nat.pow_succ]
    rw [hpow]
    omega
  have hlower : popCount (2^A-3) = A-1 := by
    rw [hlowerForm, popCount_two_mul_add_one,
      popCount_pow_two_sub_two (A-1) (by omega)]
    omega
  rw [hdecomp, hshift, hupper, hlower]
  omega

/-- Powers 2^(2k) are congruent to one modulo three. -/
theorem pow_two_even_mod_three (k : Nat) : 2^(2*k)%3 = 1 := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hexp : 2*(k+1)=2*k+2 := by omega
    calc
      2^(2*(k+1))%3 = (2^(2*k)*2^2)%3 := by
        congr 1
        rw [hexp, Nat.pow_add]
      _ = (2^(2*k)%3)*(2^2%3)%3 := by rw [Nat.mul_mod]
      _ = 1 := by rw [ih]

/-- For even L, the q4 terminal dispatcher length is a multiple of three. -/
theorem q4_terminal_index_mod_three (A L : Nat) (hL : L%2=0) :
    (2^A*(2^(L+2)-1)-3)%3 = 0 := by
  have hLdiv : L=2*(L/2) := by
    have h := Nat.mod_add_div L 2
    rw [hL] at h
    omega
  let k : Nat := L/2
  have hk : L=2*k := by exact hLdiv
  have hpowmod : 2^(L+2)%3=1 := by
    rw [hk]
    have hexp : 2*k+2=2*(k+1) := by omega
    rw [hexp]
    exact pow_two_even_mod_three (k+1)
  let q : Nat := 2^(L+2)/3
  have hdivEq : 1+3*q=2^(L+2) := by
    dsimp [q]
    simpa [hpowmod] using (Nat.mod_add_div (2^(L+2)) 3)
  have hpowLarge : 3 < 2^(L+2) := by
    have h := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤L+2)
    have hfour : 4≤2^(L+2) := by
      calc
        4=2^2 := by decide
        _≤2^(L+2) := h
    omega
  have hqpos : 0<q := by
    dsimp [q]
    exact Nat.div_pos (by omega) (by decide)
  have hApos : 0<2^A := Nat.pow_pos (by decide)
  have hmulpos : 0<2^A*q := Nat.mul_pos hApos hqpos
  have hsub : 2^(L+2)-1=3*q := by omega
  have hfactor : 2^A*(2^(L+2)-1)-3 = 3*(2^A*q-1) := by
    rw [hsub]
    calc
      2^A*(3*q)-3 = (2^A*3)*q-3 := by rw [Nat.mul_assoc]
      _ = (3*2^A)*q-3 := by rw [Nat.mul_comm (2^A) 3]
      _ = 3*(2^A*q)-3 := by rw [← Nat.mul_assoc]
      _ = 3*(2^A*q-1) := by omega
  have hdvd : 3 ∣ 2^A*(2^(L+2)-1)-3 := ⟨2^A*q-1,hfactor⟩
  exact (Nat.dvd_iff_mod_eq_zero).mp hdvd

/-- Exact cost formula specialized to the arbitrary-A q4 terminal index.
The divisibility premise is discharged by 'q4_terminal_index_mod_three'
when L is even. -/
theorem sectionResult_q4_terminal_cost (A L U R : Nat) (hA : 2≤A)
    (hN : (2^A*(2^(L+2)-1)-3)%3=0) :
    (sectionResult (2^A*(2^(L+2)-1)-3) 0 U R).cost =
      31*(2^A*(2^(L+2)-1)-3) - 12*(A+L) +
        rawSum (2^A*(2^(L+2)-1)-3) 0 U R := by
  have hNdiv : 2^A*(2^(L+2)-1)-3 =
      3*((2^A*(2^(L+2)-1)-3)/3) := by omega
  rw [hNdiv]
  rw [sectionResult_cost_three_cycle]
  have hpop : popCount (3*((2^A*(2^(L+2)-1)-3)/3))=A+L := by
    rw [← hNdiv]
    exact popCount_q4_terminal_index A L hA
  rw [hpop]

/-- The q4 terminal cost specialization with its divisibility condition
proved from the even-width hypothesis. -/
theorem sectionResult_q4_terminal_cost_even (A L U R : Nat) (hA : 2≤A)
    (hL : L%2=0) :
    (sectionResult (2^A*(2^(L+2)-1)-3) 0 U R).cost =
      31*(2^A*(2^(L+2)-1)-3) - 12*(A+L) +
        rawSum (2^A*(2^(L+2)-1)-3) 0 U R := by
  exact sectionResult_q4_terminal_cost A L U R hA
    (q4_terminal_index_mod_three A L hL)

end BB6SectionResultModel

#print axioms BB6SectionResultModel.sumV2_add_popCount
#print axioms BB6SectionResultModel.sectionResult_cost_three_cycle
#print axioms BB6SectionResultModel.rawSum_add_terminalExponent
#print axioms BB6SectionResultModel.weightedEpsilonSum_three_cycle
#print axioms BB6SectionResultModel.sectionResult_one_dimensional_cost
#print axioms BB6SectionResultModel.popCount_q4_terminal_index
#print axioms BB6SectionResultModel.q4_terminal_index_mod_three
#print axioms BB6SectionResultModel.sectionResult_q4_terminal_cost
#print axioms BB6SectionResultModel.sectionResult_q4_terminal_cost_even
