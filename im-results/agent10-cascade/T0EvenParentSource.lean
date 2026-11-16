import T0EvenParentCombined
import T0EvenParentBoundary
import LevelDeficitDynamics
import ResetChain

namespace Agent10T0Parent

open CascadeResetInverse CascadeLevelDeficit CascadeSweep

/-- Fatal height in the standard six-state two-symbol source coordinates. -/
def t0FatalHeight (n : Nat) : Nat := 4 * 2^n - n - 4

/-- The even arm of the exact original first-reset grammar at level k. -/
def EvenParentAt (k h u : Nat) : Prop :=
  (6 * 2^k - 1 ≤ u ∧ u ≤ 8 * 2^k - 3) ∧
    2 * u = 8 * 2^k + h + k

/-- The t=0 odd arm of the exact original first-reset grammar at level k. -/
def OddParentAtZero (k h u d : Nat) : Prop :=
  d % 2 = 1 ∧
  (6 * 2^k + 1 ≤ d ∧ d ≤ 8 * 2^k - 1) ∧
  2 * u + 5 = 3 * d ∧
  2 * d = 8 * 2^k + h + k + 5

/-- A finite chain of genuine same-level even first-reset edges.  Each
intermediate target is required to retain first-failure level K. -/
inductive SameLevelEvenRun (K : Nat) : Nat → Nat → Nat → Prop where
  | nil (h : Nat) (hh : FirstFailureAt h K) :
      SameLevelEvenRun K 0 h h
  | step {q start h u : Nat}
      (run : SameLevelEvenRun K q start h)
      (hu : FirstFailureAt u K)
      (hp : EvenParentAt K h u) :
      SameLevelEvenRun K (q + 1) start u

theorem same_level_even_run_endpoint
    (K q start h : Nat) (hr : SameLevelEvenRun K q start h) :
    FirstFailureAt h K := by
  induction hr with
  | nil h hh => exact hh
  | step hr hu hp ih => exact hu

/-- Every edge in SameLevelEvenRun is the even arm of ResetParent. -/
theorem even_parent_at_is_reset_parent
    (K h u : Nat) (hp : EvenParentAt K h u) :
    ResetParent h u := by
  rcases hp with ⟨hband, heq⟩
  exact Or.inl ⟨K, hband, heq⟩

/-- Every t=0 odd edge in this dossier is the odd arm of ResetParent. -/
theorem odd_parent_at_zero_is_reset_parent
    (K h u d : Nat) (hp : OddParentAtZero K h u d) :
    ResetParent h u := by
  rcases hp with ⟨hd, hband, hout, hsource⟩
  exact Or.inr ⟨K, 0, d, hd, hband, hout, hsource⟩

/-- The exact deficit scaling for q same-level even reset edges. -/
theorem deficit_scaling_of_same_level_even_run
    (K q start h : Nat) (hr : SameLevelEvenRun K q start h) :
    deficit start K = 2^q * deficit h K := by
  induction hr with
  | nil h hh => simp [deficit]
  | step hr hu hp ih =>
      rcases hp with ⟨hband, heq⟩
      have hpar : (h + K) % 2 = 0 := by omega
      have hout : u = evenOutput h K := by
        dsimp [evenOutput]
        omega
      have hhalf : deficit h K = 2 * deficit u K := by
        rw [hout]
        exact even_deficit_halves h K hpar
      calc
        deficit start K = 2^q * deficit h K := ih
        _ = 2^q * (2 * deficit u K) := by rw [hhalf]
        _ = 2^(q + 1) * deficit u K := by
          rw [Nat.pow_succ]
          ring

private theorem pow2_ge_add_four (K : Nat) (hK : 4 ≤ K) :
    K + 4 ≤ 2^K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
      rw [Nat.pow_succ]
      omega

/-- A t=0 odd-reset child of a genuine level-K source is at first-failure
level K+1.  This makes the later even-run hypothesis an authentic source
section, rather than a prepared-height assumption. -/
theorem t0_odd_child_first_failure
    (K h u d : Nat)
    (hK : 266 ≤ K)
    (hh : FirstFailureAt h K)
    (hp : OddParentAtZero K h u d) :
    FirstFailureAt u (K + 1) := by
  rcases hp with ⟨hd, hband, hout, hsource⟩
  have hpar : (h + K) % 2 = 1 := by omega
  have hfactor : oddParameter h K = d := by
    dsimp [oddParameter]
    omega
  have hguards := odd_reset_guards h K 0 d hh.1 hh.2 hpar hd hfactor
  have hu : u = oddOutput 0 d := by
    dsimp [oddOutput]
    omega
  have hlow : ∀ j, j < K + 1 → 8 * 2^j ≤ u + j + 5 := by
    intro j hj
    have h := hguards j (by omega)
    rw [← hu]
    exact h
  have hup : u ≤ 12 * 2^K - 4 := by omega
  have hpow : 8 * 2^(K + 1) = 16 * 2^K := by
    rw [Nat.pow_succ]
    ring
  have hKsmall : K + 2 < 4 * 2^K := by
    have h := pow2_ge_add_four K (by omega)
    nlinarith
  have hhigh : u + (K + 1) + 5 < 8 * 2^(K + 1) := by
    rw [hpow]
    omega
  exact ⟨hlow, hhigh⟩

/-- The source equation forces 2^q | delta.  This is the divisibility
step needed to derive the two large-power inequalities from the source
band, rather than assuming them as free arithmetic hypotheses. -/
theorem t0_delta_factorization_of_equation
    (K q r delta : Nat)
    (hq : q ≤ K - 1)
    (hdelta_lo : K + 3 ≤ delta)
    (hdelta_hi : delta ≤ 2 * K + 4)
    (heq :
      (2 * K + 7) * 2^(q + r + 3) + 2^q * (2 * K + 1) =
        2^(K + q + 4) + 12 * 2^K + 3 * delta) :
    ∃ e, 0 < e ∧ delta = 2^q * e := by
  have hpowA : 2^q * 2^(r + 3) = 2^(q + r + 3) := by
    calc
      2^q * 2^(r + 3) = 2^(q + (r + 3)) := (Nat.pow_add 2 q (r + 3)).symm
      _ = 2^(q + r + 3) := by congr 1 <;> omega
  have hpowB : 2^q * 2^(K + 4) = 2^(K + q + 4) := by
    calc
      2^q * 2^(K + 4) = 2^(q + (K + 4)) := (Nat.pow_add 2 q (K + 4)).symm
      _ = 2^(K + q + 4) := by congr 1 <;> omega
  have hpowC : 2^q * 2^(K - q) = 2^K := by
    calc
      2^q * 2^(K - q) = 2^(q + (K - q)) := (Nat.pow_add 2 q (K - q)).symm
      _ = 2^K := by congr 1 <;> omega
  have hfact :
      2^q * ((2 * K + 7) * 2^(r + 3) + (2 * K + 1)) =
        2^q * (2^(K + 4) + 12 * 2^(K - q)) + 3 * delta := by
    calc
      _ = (2 * K + 7) * (2^q * 2^(r + 3)) + 2^q * (2 * K + 1) := by ring
      _ = (2 * K + 7) * 2^(q + r + 3) + 2^q * (2 * K + 1) := by rw [hpowA]
      _ = 2^(K + q + 4) + 12 * 2^K + 3 * delta := heq
      _ = 2^q * (2^(K + 4) + 12 * 2^(K - q)) + 3 * delta := by
        rw [← hpowB, ← hpowC]
        ring
  have hdivsum :
      2^q ∣ 2^q * (2^(K + 4) + 12 * 2^(K - q)) + 3 * delta := by
    rw [← hfact]
    exact ⟨(2 * K + 7) * 2^(r + 3) + (2 * K + 1), rfl⟩
  have hdivshift :
      2^q ∣ 2^q * (2^(K + 4) + 12 * 2^(K - q)) :=
    ⟨2^(K + 4) + 12 * 2^(K - q), rfl⟩
  have hdiv : 2^q ∣ 3 * delta :=
    (Nat.dvd_add_iff_left hdivshift).mp hdivsum
  have hcop : Nat.Coprime (2^q) 3 := Nat.Coprime.pow_left q (by decide)
  have hdiv_delta : 2^q ∣ delta := hcop.dvd_of_dvd_mul_left hdiv
  obtain ⟨e, he⟩ := hdiv_delta
  have hepos : 0 < e := by
    by_contra h
    have he0 : e = 0 := by omega
    rw [he0] at he
    omega
  exact ⟨e, hepos, he⟩

/--
Source-connected t=0 adjacent-fatal exclusion.

The hypotheses are exact original ResetParent edges: an entry E at level K
has an even parent at level K-1; q genuine same-level even resets lead to
the t=0 odd source h; its child u undergoes r genuine same-level even resets;
and the final even edge reaches the original fatal height F_(K+2).
The theorem proves this configuration impossible for K>=266.
-/
theorem t0_adjacent_fatal_no_even_entry_parent
    (K q r E P h u x d : Nat)
    (hK : 266 ≤ K)
    (hEntry : FirstFailureAt E K)
    (hEntryParent : EvenParentAt (K - 1) P E)
    (hPrefix : SameLevelEvenRun K q E h)
    (hOdd : OddParentAtZero K h u d)
    (hTail : SameLevelEvenRun (K + 1) r u x)
    (hFatalExit :
      EvenParentAt (K + 1) x (t0FatalHeight (K + 2))) :
    False := by
  rcases hEntryParent with ⟨hEntryBand, hEntryEquation⟩
  rcases hOdd with ⟨hd, hOddBand, hOddOutput, hOddSource⟩
  rcases hFatalExit with ⟨hFatalBand, hFatalEquation⟩
  have hSourceLevel : FirstFailureAt h K :=
    same_level_even_run_endpoint K q E h hPrefix
  have hChildLevel : FirstFailureAt u (K + 1) :=
    t0_odd_child_first_failure K h u d hK hSourceLevel
      ⟨hd, hOddBand, hOddOutput, hOddSource⟩
  have hFinalDeficit : deficit x (K + 1) = 4 * K + 14 := by
    have hpK1 : 2^(K + 1) = 2 * 2^K := by rw [Nat.pow_succ]
    have hpK2 : 2^(K + 2) = 4 * 2^K := by
      rw [Nat.pow_add]
      norm_num
    have hF : t0FatalHeight (K + 2) =
        16 * 2^K - K - 6 := by
      dsimp [Agent10T1Fatal.fatalHeight]
      rw [hpK2]
      omega
    have hx : x = 16 * 2^K - 3 * K - 13 := by
      rw [hF, hpK1] at hFatalEquation
      omega
    dsimp [deficit]
    rw [hpK1, hx]
    omega
  have hTailScale :=
    deficit_scaling_of_same_level_even_run (K + 1) r u x hTail
  have hChildDeficit : deficit u (K + 1) = 2^r * (4 * K + 14) := by
    rw [hFinalDeficit] at hTailScale
    exact hTailScale
  have hFatalEquation' :
      3 * d + 2^(r + 1) * (4 * K + 14) =
        32 * 2^K + 2 * K + 7 := by
    have hmul := congrArg (fun z => 2 * z) hChildDeficit
    dsimp [deficit] at hmul
    have hpK1 : 2^(K + 1) = 2 * 2^K := by rw [Nat.pow_succ]
    rw [hpK1] at hmul
    have hpR : 2 * 2^r = 2^(r + 1) := by rw [Nat.pow_succ]
    rw [hpR] at hmul
    omega
  have hD0formula :
      deficit h K + 2 * d = 16 * 2^K + 2 * K + 5 := by
    dsimp [deficit]
    omega
  have hD0lower : 2 * K + 7 ≤ deficit h K := by
    have hdUpper := hOddBand.2
    omega
  have hPrefixScale :=
    deficit_scaling_of_same_level_even_run K q E h hPrefix
  have hFirstLow := first_low E K hEntry.1
  have hDentryUpper : deficit E K ≤ 4 * 2^K + 2 * K + 4 := by
    dsimp [deficit]
    omega
  have hq : q ≤ K - 1 := by
    by_contra hnot
    have hq' : K ≤ q := by omega
    have hpq : 2^K ≤ 2^q := Nat.pow_le_pow_right (by omega) hq'
    have hmul :
        2^K * (2 * K + 7) ≤ 2^q * deficit h K :=
      Nat.mul_le_mul hpq hD0lower
    rw [← hPrefixScale] at hmul
    nlinarith [hmul, hDentryUpper, hK]
  have hEntryLower : 4 * 2^K + K + 3 ≤ deficit E K := by
    have hpK : 2^K = 2 * 2^(K - 1) := by
      have h : (K - 1) + 1 = K := by omega
      rw [← h, Nat.pow_succ]
      ring
    have hUpper : E ≤ 4 * 2^K - 3 := by
      rw [hpK]
      omega
    dsimp [deficit]
    omega
  let delta : Nat := deficit E K - 4 * 2^K
  have hDeltaBase : 4 * 2^K ≤ deficit E K := by omega
  have hDentry : deficit E K = 4 * 2^K + delta := by
    dsimp [delta]
    omega
  have hdeltaLo : K + 3 ≤ delta := by
    rw [← hDentry] at hEntryLower
    omega
  have hdeltaHi : delta ≤ 2 * K + 4 := by
    rw [← hDentry] at hDentryUpper
    omega
  have hbandR :
      8 * 2^K + (2 * K + 7) + 3 ≤ (2 * K + 7) * 2^(r + 2) := by
    have htailPow :
        2^(r + 1) * (4 * K + 14) = (2 * K + 7) * 2^(r + 2) := by
      rw [Nat.pow_succ]
      ring
    rw [← htailPow]
    omega
  have hD0Equation :
      3 * deficit h K + 16 * 2^K =
        (2 * K + 7) * 2^(r + 3) + 2 * K + 1 := by
    have hFatalDouble := congrArg (fun z => 2 * z) hFatalEquation'
    have hTailDouble :
        2^(r + 2) * (4 * K + 14) = (2 * K + 7) * 2^(r + 3) := by
      rw [Nat.pow_succ]
      ring
    nlinarith [hD0formula, hFatalDouble, hTailDouble]
  have hpowA : 2^q * 2^(r + 3) = 2^(q + r + 3) := by
    calc
      2^q * 2^(r + 3) = 2^(q + (r + 3)) := (Nat.pow_add 2 q (r + 3)).symm
      _ = 2^(q + r + 3) := by congr 1 <;> omega
  have hpowB : 2^q * 2^K = 2^(K + q) := by
    calc
      2^q * 2^K = 2^(q + K) := (Nat.pow_add 2 q K).symm
      _ = 2^(K + q) := by congr 1 <;> omega
  have hDentryScale : 2^q * deficit h K = 4 * 2^K + delta := by
    rw [← hPrefixScale, hDentry]
  have hmulD0 :
      2^q * (3 * deficit h K + 16 * 2^K) =
        2^q * ((2 * K + 7) * 2^(r + 3) + 2 * K + 1) := by
    rw [hD0Equation]
  have hleft :
      2^q * (3 * deficit h K + 16 * 2^K) =
        12 * 2^K + 3 * delta + 2^(K + q + 4) := by
    rw [Nat.mul_add, Nat.mul_add]
    rw [hDentryScale, hpowB]
    ring
  have hright :
      2^q * ((2 * K + 7) * 2^(r + 3) + 2 * K + 1) =
        (2 * K + 7) * 2^(q + r + 3) + 2^q * (2 * K + 1) := by
    rw [Nat.mul_add, hpowA]
  have heq :
      (2 * K + 7) * 2^(q + r + 3) + 2^q * (2 * K + 1) =
        2^(K + q + 4) + 12 * 2^K + 3 * delta := by
    calc
      _ = 2^q * ((2 * K + 7) * 2^(r + 3) + 2 * K + 1) := hright.symm
      _ = 2^q * (3 * deficit h K + 16 * 2^K) := hmulD0.symm
      _ = 12 * 2^K + 3 * delta + 2^(K + q + 4) := hleft
      _ = 2^(K + q + 4) + 12 * 2^K + 3 * delta := by omega
  obtain ⟨e, hepos, he⟩ :=
    t0_delta_factorization_of_equation K q r delta hq hdeltaLo hdeltaHi heq
  have hpower := t0_entry_even_parent_power_bounds K q r e delta
    (by omega) hq hepos he hdeltaHi hbandR
  exact t0_entry_even_parent_arithmetic_no_solution K q r delta
    hK hq hdeltaLo hdeltaHi hpower.1 hpower.2 heq

#print axioms t0_odd_child_first_failure
#print axioms deficit_scaling_of_same_level_even_run
#print axioms t0_delta_factorization_of_equation
#print axioms t0_adjacent_fatal_no_even_entry_parent

end Agent10T0Parent
