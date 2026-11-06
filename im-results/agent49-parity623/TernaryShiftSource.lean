import Agent49ParitySource

/-!
Sharp first-counter translation for the #623 original DeepMind accelerated drain.
This proof imports unmodified source definitions through Agent49ParitySource
(which itself imports BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA)
and reuses its source-proved ternary budget.
Original source: google-deepmind/cryptids@c86f15861709b76042998c5211c7b2f83991621b.
No machine halting/nonhalting conclusion follows from this conditional local theorem.
-/

namespace BB6.Agent49TernaryShiftSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource

def liftFirstEval (t : Nat) : Nat × Nat × Nat → Nat × Nat × Nat
  | (a,b,d) => (a+t,b,d)

def liftFirstState (t : Nat) : HighLevelState → HighLevelState
  | .D a d => .D (a+t) d

/-- Under the exponentially large sharp ones-budget, increasing the first
evaluator counter commutes with evaluation, keeping the other coordinates. -/
theorem evalA_shift_ones (a : Nat) : ∀ k m t : Nat, k < ternaryOnes a →
    evalA (a+t) k m = (evalA a k m).map (liftFirstEval t) := by
  induction a with
  | zero =>
    intro k m t hk
    simp [ternaryOnes] at hk
  | succ a ih =>
    intro k m t hk
    have ht : (a+1)+t=(a+t)+1 := by omega
    rw [ht]
    conv => lhs; rw [evalA]
    conv => rhs; rw [evalA]
    by_cases h2 : k%3=2
    · simp only [if_pos h2, Option.map_some, liftFirstEval]
      congr 1
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    · simp only [if_neg h2]
      have hpos1 : (a+t)+1 ≠ 0 := by omega
      have hpos2 : a+1 ≠ 0 := by omega
      simp only [if_neg hpos1, if_neg hpos2]
      by_cases h0 : k%3=0
      · simp only [if_pos h0, Option.map_some, liftFirstEval]
        congr 1
      · simp only [if_neg h0]
        have hnew : k/3 < ternaryOnes a := by
          simp only [ternaryOnes] at hk
          omega
        have hsub1 : (a+t+1)-1=a+t := by omega
        have hsub2 : (a+1)-1=a := by omega
        rw [hsub1,hsub2]
        exact ih (k/3) (m+2*(k/3)+3) t hnew

/-- Exponential first-counter shift: for all b≤(3^a−1)/2, changing
a to a+t adds exactly t to the terminal first counter, preserving the
terminal second counter, for the unchanged original #623 drain. -/
theorem drainB_shift_ones (b : Nat) : ∀ a d t : Nat, b ≤ ternaryOnes a →
    drainB (a+t) b d = (drainB a b d).map (liftFirstState t) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a d t hbound
    conv => lhs; rw [drainB]
    conv => rhs; rw [drainB]
    by_cases hb : b=0
    · simp [hb,liftFirstState]
    · simp only [if_neg hb]
      have hk : b-1 < ternaryOnes a := by omega
      obtain ⟨aa,bb,dd,he,hp⟩ := evalA_ones_budget a (b-1) (d+2*b+3) hk
      have hdec : bb < b := by
        have hle := evalA_b_le_k a (b-1) (d+2*b+3) aa bb dd he
        omega
      have hshift := evalA_shift_ones a (b-1) (d+2*b+3) t hk
      rw [hshift,he]
      simp only [Option.map_some, liftFirstEval, Option.bind_some, if_pos hdec]
      exact ih bb hdec aa dd t hp

/-- Sharpness: at the first excluded b the unshifted drain halts,
whereas incrementing a by one makes the drain succeed. -/
theorem drainB_shift_ones_sharp (a d : Nat) :
    drainB (a+1) (ternaryOnes a+1) d ≠
    (drainB a (ternaryOnes a+1) d).map (liftFirstState 1) := by
  have hn := drainB_first_halt a d
  have hbudget : ternaryOnes a+1 ≤ ternaryOnes (a+1) := by
    simp only [ternaryOnes]
    omega
  obtain ⟨aa,dd,hs⟩ := drainB_safe_ones (ternaryOnes a+1) (a+1) d hbudget
  rw [hn,hs]
  simp

#print axioms evalA_shift_ones
#print axioms drainB_shift_ones
#print axioms drainB_shift_ones_sharp
end BB6.Agent49TernaryShiftSource
