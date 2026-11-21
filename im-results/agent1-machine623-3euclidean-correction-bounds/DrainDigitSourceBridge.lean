import Agent41DrainValuationNormalForm
import Agent22ExactDrainCocycleSource
import Agent1SignedCoordinateNormalForm

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace BB6.Agent1DrainDigitSourceBridge

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent41DrainValuationNormalForm
open BB6.Agent22ExactDrainCocycleSource

theorem ternaryOnes_mono : ∀ {a b : Nat}, a ≤ b →
    ternaryOnes a ≤ ternaryOnes b := by
  intro a b hab
  induction hab with
  | refl => exact Nat.le_refl _
  | @step b h ih =>
      simp [ternaryOnes]
      omega

/--
Split one source drain parameter b by the low-order run of ternary ones
in b-1. The returned triple is (v,q,eps) with
b-1 = ternaryOnes v + 3^v * (3*q + 2*eps).
This is exactly the decomposition consumed by the original evalA.
-/
def sourceDrainStep (k : Nat) : Nat × Nat × Nat :=
  if k % 3 = 1 then
    let t := sourceDrainStep (k / 3)
    (t.1 + 1, t.2.1, t.2.2)
  else
    (0, k / 3, (k % 3) / 2)
termination_by k
decreasing_by omega

theorem sourceDrainStep_spec (k : Nat) :
    let t := sourceDrainStep k
    t.2.2 ≤ 1 ∧
      k = ternaryOnes t.1 + 3^t.1 * (3*t.2.1 + 2*t.2.2) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
    rw [sourceDrainStep.eq_1]
    by_cases h1 : k % 3 = 1
    · simp only [if_pos h1]
      let t := sourceDrainStep (k / 3)
      have hi := ih (k/3) (by omega)
      change t.2.2 ≤ 1 ∧ k/3 =
        ternaryOnes t.1 + 3^t.1*(3*t.2.1+2*t.2.2) at hi
      rcases hi with ⟨he,hk⟩
      constructor
      · exact he
      · have hpow : 3^(t.1+1) = 3*3^t.1 := by
          rw [Nat.pow_succ]
          omega
        have hones : ternaryOnes (t.1+1) = 3*ternaryOnes t.1+1 := rfl
        have hmod : k = 3*(k/3)+1 := by omega
        calc
          k = 3*(k/3)+1 := hmod
          _ = 3*(ternaryOnes t.1 + 3^t.1*(3*t.2.1+2*t.2.2))+1 := by rw [hk]
          _ = ternaryOnes (t.1+1) + 3^(t.1+1)*(3*t.2.1+2*t.2.2) := by
            rw [hones,hpow]
            simp [Nat.mul_add,Nat.mul_assoc,Nat.add_assoc,Nat.add_comm]
    · simp only [if_neg h1]
      dsimp
      have hr : k%3=0 ∨ k%3=2 := by omega
      rcases hr with h0 | h2
      · simp [h0,ternaryOnes]
        omega
      · simp [h2,ternaryOnes]
        omega

theorem sourceDrainStep_q_lt (k : Nat) :
    (sourceDrainStep k).2.1 < k+1 := by
  have h := sourceDrainStep_spec k
  dsimp at h
  rcases h with ⟨he,hk⟩
  have hpow : 1 ≤ 3^(sourceDrainStep k).1 :=
    Nat.one_le_pow _ _ (by decide)
  have hsum :
      3*(sourceDrainStep k).2.1 ≤
        3*(sourceDrainStep k).2.1 + 2*(sourceDrainStep k).2.2 := by omega
  have hmul0 := Nat.mul_le_mul hpow hsum
  have hmul :
      3*(sourceDrainStep k).2.1 ≤
        3^(sourceDrainStep k).1 *
          (3*(sourceDrainStep k).2.1+2*(sourceDrainStep k).2.2) := by
    simpa using hmul0
  omega

/--
The exact source drain statistics (L,E,R): L is the sum of consumed
low-one-run lengths plus one per call; E counts steps whose next ternary
digit is 2; R counts actual evaluator calls, one per successful drainB
iteration.
-/
def sourceDrainSummary (b : Nat) : Nat × Nat × Nat :=
  match b with
  | 0 => (0,0,0)
  | b+1 =>
    let t := sourceDrainStep b
    let u := sourceDrainSummary t.2.1
    (t.1+1+u.1, t.2.2+u.2.1, 1+u.2.2)
termination_by b
decreasing_by exact sourceDrainStep_q_lt b

def sourceDrainLength (b : Nat) : Nat := (sourceDrainSummary b).1
def sourceDrainTwos (b : Nat) : Nat := (sourceDrainSummary b).2.1
def sourceDrainCalls (b : Nat) : Nat := (sourceDrainSummary b).2.2

/--
The source-drain recursion consumes at most n levels whenever 2*b < 3^n.
For t = sourceDrainStep (b-1) = (v,q,eps), the key identity is
2*b-1 = 3^v * (6*q + 4*eps + 1), while the summary length recurs as
L(b) = v+1+L(q).
-/
theorem ternaryOnes_double_add_one (n : Nat) :
    2 * ternaryOnes n + 1 = 3^n := by
  induction n with
  | zero => simp [ternaryOnes]
  | succ n ih =>
      have hrec : ternaryOnes (n+1) = 3*ternaryOnes n+1 := rfl
      rw [hrec, Nat.pow_succ]
      omega

theorem sourceDrainLength_le_of_two_mul_lt_pow (b : Nat) :
    ∀ n : Nat, 2*b < 3^n → sourceDrainLength b ≤ n := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro n hpow
    cases b with
    | zero => simp [sourceDrainLength, sourceDrainSummary]
    | succ b =>
      let t := sourceDrainStep b
      have ht : t.2.2 ≤ 1 ∧
          b = ternaryOnes t.1 + 3^t.1*(3*t.2.1+2*t.2.2) := by
        simpa [t] using sourceDrainStep_spec b
      rcases ht with ⟨heps,hdec⟩
      have hfactor : 2*b+1 =
          3^t.1*(6*t.2.1+4*t.2.2+1) := by
        calc
          2*b+1 = 2*(ternaryOnes t.1 +
              3^t.1*(3*t.2.1+2*t.2.2))+1 := by rw [hdec]
          _ = (2*ternaryOnes t.1+1) +
              3^t.1*(6*t.2.1+4*t.2.2) := by
                have h1 : 2*(2*3^t.1) = 3^t.1*4 := by omega
                have h2 : 2*(3*3^t.1) = 3^t.1*6 := by omega
                simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm,
                  Nat.mul_comm, Nat.add_assoc, Nat.add_comm, h1, h2]
          _ = 3^t.1*(6*t.2.1+4*t.2.2+1) := by
              rw [ternaryOnes_double_add_one]
              simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      have hlarge : 2*b+1 < 3^n := by omega
      have hfacpos : 1 ≤ 6*t.2.1+4*t.2.2+1 := by omega
      have hpowv : 3^t.1 < 3^n := by
        calc
          3^t.1 ≤ 3^t.1*(6*t.2.1+4*t.2.2+1) := by
            simpa using Nat.mul_le_mul_left (3^t.1) hfacpos
          _ = 2*b+1 := hfactor.symm
          _ < 3^n := hlarge
      have hv : t.1 < n :=
        (Nat.pow_lt_pow_iff_right (by decide : 1<(3:Nat))).mp hpowv
      have hpoweq : 3^n = 3^t.1*3^(n-t.1) := by
        rw [← Nat.pow_add]
        congr 1
        omega
      have hfactor_lt :
          6*t.2.1+4*t.2.2+1 < 3^(n-t.1) := by
        apply (Nat.mul_lt_mul_left
          (Nat.pow_pos (by decide : 0<(3:Nat)))).mp
        calc
          3^t.1*(6*t.2.1+4*t.2.2+1) = 2*b+1 := hfactor.symm
          _ < 3^n := hlarge
          _ = 3^t.1*3^(n-t.1) := hpoweq
      have hpow3 : 3^(n-t.1) = 3*3^(n-t.1-1) := by
        have hsub : n-t.1 = (n-t.1-1)+1 := by omega
        rw [hsub, Nat.pow_succ]
        exact Nat.mul_comm _ _
      have hqpow : 2*t.2.1 < 3^(n-t.1-1) := by
        rw [hpow3] at hfactor_lt
        omega
      have hq_lt : t.2.1 < b+1 := by
        simpa [t] using sourceDrainStep_q_lt b
      have hi := ih t.2.1 hq_lt (n-t.1-1) hqpow
      have hrec : sourceDrainLength (b+1) =
          t.1+1+sourceDrainLength t.2.1 := by
        simp [sourceDrainLength, sourceDrainSummary, t]
      rw [hrec]
      omega

/--
Mass-index wrapper: if 2*b is at most S+6 and the mass index ell satisfies
2*S+7 <= 3^ell, then the source-drain length is at most ell.
-/
theorem sourceDrainLength_le_of_mass_index
    (S b ell : Nat) (hb : 2*b ≤ S+6) (hmass : 2*S+7 ≤ 3^ell) :
    sourceDrainLength b ≤ ell := by
  apply sourceDrainLength_le_of_two_mul_lt_pow
  omega


theorem sourceDrainSummary_bounds (b : Nat) :
    sourceDrainTwos b ≤ sourceDrainCalls b ∧
    sourceDrainCalls b ≤ sourceDrainLength b := by
  change (sourceDrainSummary b).2.1 ≤ (sourceDrainSummary b).2.2 ∧
    (sourceDrainSummary b).2.2 ≤ (sourceDrainSummary b).1
  induction b using Nat.strongRecOn with
  | ind b ih =>
    cases b with
    | zero => simp [sourceDrainSummary]
    | succ b =>
      simp only [sourceDrainSummary]
      have ht := sourceDrainStep_spec b
      change (sourceDrainStep b).2.2 ≤ 1 ∧ b =
        ternaryOnes (sourceDrainStep b).1 + 3^(sourceDrainStep b).1 *
          (3*(sourceDrainStep b).2.1+2*(sourceDrainStep b).2.2) at ht
      have hi := ih (sourceDrainStep b).2.1 (sourceDrainStep_q_lt b)
      rcases ht with ⟨he,hk⟩
      rcases hi with ⟨hER,hRL⟩
      constructor <;> omega

theorem sourceDrainStats_bounds (b : Nat) :
    0 ≤ (sourceDrainTwos b : Int) ∧
    (sourceDrainTwos b : Int) ≤ sourceDrainCalls b ∧
    (sourceDrainCalls b : Int) ≤ sourceDrainLength b := by
  unfold sourceDrainTwos sourceDrainCalls sourceDrainLength
  have h := sourceDrainSummary_bounds b
  omega

/--
The actual source drain has first-counter drop L-2E and exactly R
evaluator calls. In the right-even bundled ray the initial evaluator is
already inside the supplied drain parameter, so it is counted here too.
-/
theorem drainB_digit_cocycle (b : Nat) :
    ∀ a d aa dd, b ≤ ternaryOnes a →
      drainB a b d = some (.D aa dd) →
      aa + sourceDrainLength b = a + 2*sourceDrainTwos b ∧
      2*aa+dd = 2*a+d+3*b+2*sourceDrainCalls b := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d aa dd hbudget hrun
    cases b with
    | zero =>
      simp [drainB,sourceDrainSummary] at hrun
      rcases hrun with ⟨rfl,rfl⟩
      simp [sourceDrainLength,sourceDrainTwos,sourceDrainCalls,sourceDrainSummary]
    | succ b =>
      rw [drainB] at hrun
      have hb : b+1 ≠ 0 := by omega
      simp only [if_neg hb] at hrun
      let t := sourceDrainStep b
      have ht := sourceDrainStep_spec b
      change t.2.2 ≤ 1 ∧ b =
        ternaryOnes t.1 + 3^t.1*(3*t.2.1+2*t.2.2) at ht
      rcases ht with ⟨heps,hdec⟩
      have hstepbudget : b < ternaryOnes a := by omega
      have htv : ternaryOnes t.1 ≤ b := by
        rw [hdec]
        exact Nat.le_add_right _ _
      have hv : t.1 < a := by
        by_cases hnot : a ≤ t.1
        · have hmono := ternaryOnes_mono hnot
          omega
        · omega
      have hstep : t.1+1-t.2.2 ≤ a := by omega
      let m := d+2*(b+1)+3
      have hEval := evalA_3adic_run a b m t.1 t.2.1 t.2.2 heps hdec hstep
      have hEvalBudget := evalA_ones_budget a b m hstepbudget
      rcases hEvalBudget with ⟨a2,q2,d2,he2,hp⟩
      rw [hEval] at he2
      have heq := Option.some.inj he2
      cases heq
      have hq : t.2.1 < b+1 := sourceDrainStep_q_lt b
      dsimp [m] at hEval
      have hsub : b+1-1=b := by omega
      rw [hsub] at hrun
      rw [hEval] at hrun
      simp only [Option.bind_some] at hrun
      rw [if_pos hq] at hrun
      have hi := ih t.2.1 hq
        (a+2*t.2.2-(t.1+1))
        (d+2*(b+1)+3+
          (6*t.2.1+1+4*t.2.2)*ternaryOnes t.1+
          2*t.1+2*(1-t.2.2))
        aa dd hp hrun
      rcases hi with ⟨hfirst,hweighted⟩
      have hstepWeighted := evalA_weighted_exact a b m
        (a+2*t.2.2-(t.1+1)) t.2.1
        (m+(6*t.2.1+1+4*t.2.2)*ternaryOnes t.1+
          2*t.1+2*(1-t.2.2))
        hstepbudget hEval
      rw [sourceDrainSummary.eq_2]
      let u := sourceDrainSummary t.2.1
      change aa + (t.1+1+u.1) = a + 2*(t.2.2+u.2.1) ∧
        2*aa+dd = 2*a+d+3*(b+1)+2*(1+u.2.2)
      change aa+u.1 = (a+2*t.2.2-(t.1+1))+2*u.2.1 at hfirst
      change 2*aa+dd = 2*(a+2*t.2.2-(t.1+1)) +
        (m+(6*t.2.1+1+4*t.2.2)*ternaryOnes t.1+
          2*t.1+2*(1-t.2.2)) + 3*t.2.1+2*u.2.2 at hweighted
      have hsum : 2*aa+dd = 2*a+b+m+2*u.2.2 := by omega
      dsimp [m] at hsum
      constructor <;> omega

theorem drainB_full_count_eq_summary (b : Nat) :
    ∀ a d aa dd, b ≤ ternaryOnes a →
      drainB a b d = some (.D aa dd) →
      ∃ r : Nat,
        2*aa+dd = 2*a+d+3*b+2*r ∧ r = sourceDrainCalls b := by
  intro a d aa dd hbudget hrun
  obtain ⟨r,hr⟩ := drainB_weighted_exact b a d aa dd hbudget hrun
  have hstats := drainB_digit_cocycle b a d aa dd hbudget hrun
  refine ⟨r,hr,?_⟩
  omega

theorem drainB_correction_bounds (b : Nat) (s : Sector) (br : Branch) :
    -(34*(sourceDrainLength b : Int)+122) ≤
      corrC s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
        (sourceDrainCalls b : Int) ∧
    corrC s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
      (sourceDrainCalls b : Int) ≤ 34*(sourceDrainLength b : Int)+122 ∧
    -(24*(sourceDrainLength b : Int)+84) ≤
      corrF s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
        (sourceDrainCalls b : Int) ∧
    corrF s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
      (sourceDrainCalls b : Int) ≤ 24*(sourceDrainLength b : Int)+84 := by
  have hb := sourceDrainStats_bounds b
  exact correction_count_bounds s br (sourceDrainLength b : Int)
    (sourceDrainTwos b : Int) (sourceDrainCalls b : Int) hb.1 hb.2.1 hb.2.2

theorem drainB_signed_correction_interface (b : Nat) (s : Sector) (br : Branch) :
    ∀ a d aa dd, b ≤ ternaryOnes a →
      drainB a b d = some (.D aa dd) →
      aa + sourceDrainLength b = a + 2*sourceDrainTwos b ∧
      2*aa+dd = 2*a+d+3*b+2*sourceDrainCalls b ∧
      (-(34*(sourceDrainLength b : Int)+122) ≤
        corrC s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
          (sourceDrainCalls b : Int) ∧
       corrC s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
          (sourceDrainCalls b : Int) ≤ 34*(sourceDrainLength b : Int)+122 ∧
       -(24*(sourceDrainLength b : Int)+84) ≤
        corrF s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
          (sourceDrainCalls b : Int) ∧
       corrF s br ((sourceDrainLength b : Int)-2*(sourceDrainTwos b : Int))
          (sourceDrainCalls b : Int) ≤ 24*(sourceDrainLength b : Int)+84)) := by
  intro a d aa dd hbudget hrun
  have hsource := drainB_digit_cocycle b a d aa dd hbudget hrun
  have hcorr := drainB_correction_bounds b s br
  exact ⟨hsource.1,hsource.2,hcorr⟩

#print axioms drainB_digit_cocycle
#print axioms drainB_full_count_eq_summary
#print axioms drainB_signed_correction_interface

end BB6.Agent1DrainDigitSourceBridge
