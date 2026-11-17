import Lean

/-!
A standalone formal bound for the exact recursive fatal-counter predicate
used in FullFailureSpectrumSource.lean.

The definition of badAll below is copied verbatim (modulo whitespace) from
BB6.Agent49FullSpectrum.badAll at:
  im-results/agent49-parity623/FullFailureSpectrumSource.lean

That source file proves flat_failure:
  flatB a b d = none ↔ badAll a b = true
and imports flatB_eq_drainB, so this lemma can be transferred directly to
the original Cryptids #623 drain. See the accompanying README for the
source-connected corollary and limitations.
-/

namespace BB6.Agent32FailureBudgetBound

def tau : Nat → Nat
| 0 => 0
| k + 1 => 3 * tau k + 1

/-- Exact fatality predicate from Agent49FullSpectrum. -/
def badAll (a b : Nat) : Bool :=
  if b = 0 then false
  else if b % 3 = 0 then badAll (a + 1) (b / 3 - 1)
  else if b % 3 = 1 then
    if a = 0 then true else badAll (a - 1) (b / 3)
  else
    if a = 0 then badAll 0 (b / 3) else badAll (a - 1) (b / 3 + 1)
termination_by b
  decreasing_by all_goals omega

/--
The two-sided induction invariant needed at the residue-two boundary:
below tau (k+1), fatal first counters are at most k; at the boundary
b=tau (k+1), they are also at most k.
-/
theorem badAll_bounds : ∀ k,
    (∀ a b, b < tau (k + 1) → badAll a b = true → a ≤ k) ∧
    (∀ a, badAll a (tau (k + 1)) = true → a ≤ k) := by
  intro k
  induction k with
  | zero =>
      constructor
      · intro a b hb h
        have hb0 : b = 0 := by simpa [tau] using hb
        subst b
        simp [badAll] at h
      · intro a h
        have ht : tau 1 = 1 := by rfl
        rw [ht, badAll.eq_1] at h
        have hpos : (1 : Nat) ≠ 0 := by omega
        have hmod0 : (1 : Nat) % 3 ≠ 0 := by omega
        have hmod1 : (1 : Nat) % 3 = 1 := by omega
        rw [if_neg hpos, if_neg hmod0, if_pos hmod1] at h
        by_cases ha : a = 0
        · omega
        · have hfalse : badAll (a - 1) 0 = false := by simp [badAll]
          simp [ha, hfalse] at h
  | succ k ih =>
      rcases ih with ⟨ihP, ihS⟩
      constructor
      · intro a b hb h
        have hb' : b < 3 * tau (k + 1) + 1 := by simpa [tau] using hb
        have hpos : b ≠ 0 := by
          intro hz
          subst b
          simp [badAll] at h
        have hdecomp : b = 3 * (b / 3) + b % 3 := by omega
        cases hrem : b % 3 with
        | zero =>
            have hrec : badAll (a + 1) (b / 3 - 1) = true := by
              rw [badAll.eq_1, if_neg hpos, if_pos hrem] at h
              exact h
            have hbound : b / 3 - 1 < tau (k + 1) := by omega
            have hle := ihP (a + 1) (b / 3 - 1) hbound hrec
            omega
        | succ r =>
            have hr : r < 2 := by omega
            cases r with
            | zero =>
                have hrec : (if a = 0 then true else badAll (a - 1) (b / 3)) = true := by
                  have hrem0 : b % 3 ≠ 0 := by omega
                  rw [badAll.eq_1, if_neg hpos, if_neg hrem0, if_pos hrem] at h
                  exact h
                by_cases ha : a = 0
                · omega
                · have hrec' : badAll (a - 1) (b / 3) = true := by simpa [ha] using hrec
                  have hbound : b / 3 < tau (k + 1) := by omega
                  have hle := ihP (a - 1) (b / 3) hbound hrec'
                  omega
            | succ r' =>
                have hr' : r' = 0 := by omega
                subst r'
                have hrec : (if a = 0 then badAll 0 (b / 3) else badAll (a - 1) (b / 3 + 1)) = true := by
                  have hrem0 : b % 3 ≠ 0 := by omega
                  have hrem1 : b % 3 ≠ 1 := by omega
                  rw [badAll.eq_1, if_neg hpos, if_neg hrem0, if_neg hrem1] at h
                  exact h
                by_cases ha : a = 0
                · have hrec' : badAll 0 (b / 3) = true := by simpa [ha] using hrec
                  have hbound : b / 3 < tau (k + 1) := by omega
                  have hle := ihP 0 (b / 3) hbound hrec'
                  omega
                · have hrec' : badAll (a - 1) (b / 3 + 1) = true := by simpa [ha] using hrec
                  have hboundary : b / 3 + 1 ≤ tau (k + 1) := by omega
                  by_cases hlt : b / 3 + 1 < tau (k + 1)
                  · have hle := ihP (a - 1) (b / 3 + 1) hlt hrec'
                    omega
                  · have heq : b / 3 + 1 = tau (k + 1) := by omega
                    rw [heq] at hrec'
                    have hle := ihS (a - 1) hrec'
                    omega
      · intro a h
        have ht : tau (k + 2) = 3 * tau (k + 1) + 1 := by rfl
        rw [ht, badAll.eq_1] at h
        have hpos : 3 * tau (k + 1) + 1 ≠ 0 := by omega
        have hmod0 : (3 * tau (k + 1) + 1) % 3 ≠ 0 := by omega
        have hmod1 : (3 * tau (k + 1) + 1) % 3 = 1 := by omega
        rw [if_neg hpos, if_neg hmod0, if_pos hmod1] at h
        have hdiv : (3 * tau (k + 1) + 1) / 3 = tau (k + 1) := by omega
        rw [hdiv] at h
        by_cases ha : a = 0
        · omega
        · have hrec : badAll (a - 1) (tau (k + 1)) = true := by simpa [ha] using h
          have hle := ihS (a - 1) hrec
          omega

theorem two_tau_add_one (k : Nat) : 2 * tau k + 1 = 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [tau]
      omega

/-- If b is below the next ternary threshold, every fatal a is <= k. -/
theorem badAll_first_le_pow (a b k : Nat)
    (hpow : 2 * b + 1 < 3 ^ (k + 1))
    (hbad : badAll a b = true) : a ≤ k := by
  have ht := two_tau_add_one (k + 1)
  have hb : b < tau (k + 1) := by omega
  exact (badAll_bounds k).1 a b hb hbad

/--
Every fatal first counter is logarithmically bounded:
  badAll a b = true -> 3^a <= 2*b+1.
Equivalently, a <= floor(log_3(2*b+1)).
-/
theorem badAll_power_bound (a b : Nat) (hbad : badAll a b = true) :
    3 ^ a ≤ 2 * b + 1 := by
  by_cases hle : 3 ^ a ≤ 2 * b + 1
  · exact hle
  · have hlt : 2 * b + 1 < 3 ^ a := by omega
    by_cases ha : a = 0
    · subst a
      simp at hlt
    · have haPos : 1 ≤ a := by omega
      have hpow : 2 * b + 1 < 3 ^ ((a - 1) + 1) := by
        simpa [Nat.sub_add_cancel haPos] using hlt
      have hle' := badAll_first_le_pow a b (a - 1) hpow hbad
      omega

#print axioms badAll_bounds
#print axioms badAll_first_le_pow
#print axioms badAll_power_bound

end BB6.Agent32FailureBudgetBound
