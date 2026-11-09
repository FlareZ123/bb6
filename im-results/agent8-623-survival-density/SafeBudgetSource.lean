import Agent8DigitChargeSource

/-!
Input-specific ternary safety budget for the actual #623 complete drain.
This safety condition is an exact recursive function of the B-block count,
not a polynomial/exponential global gap approximation. It is sufficient
for every input counter and includes arbitrarily large block counts
requiring zero initial first counter. It is not a root-wide invariant.
-/
namespace BB6.Agent8SafeBudgetSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8DigitChargeSource
open BB6.Agent49FlatDrainSource

/-- Exact threshold that prevents zero-first-counter calls from taking
the residue-two exception or residue-one failure branch. Residue-zero
is allowed to start at zero because it adds one first-counter unit. -/
def safeBudget (b : Nat) : Nat :=
  if b=0 then 0
  else if b%3=0 then safeBudget (b/3-1)-1
  else if b%3=1 then safeBudget (b/3)+1
  else safeBudget (b/3+1)+1
termination_by b
  decreasing_by
    all_goals
      have hdiv : b=3*(b/3)+b%3 := by omega
      omega

/-- Every input above its exact positive-semantic prefix threshold
produces a complete B-drain. This is a universal theorem. -/
theorem safeBudget_suffices (b : Nat) :
  ∀ a : Nat, safeBudget b ≤ a → ∃ x c, digitCode a b = some (x,c) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a hs
    rw [safeBudget] at hs
    rw [digitCode]
    by_cases hz : b=0
    · simp [hz]
    · simp only [if_neg hz] at hs ⊢
      have hdiv : b=3*(b/3)+b%3 := by omega
      by_cases hr0 : b%3=0
      · simp only [if_pos hr0] at hs ⊢
        have hchild : b/3-1 < b := by omega
        have hbound : safeBudget (b/3-1) ≤ a+1 := by omega
        obtain ⟨x,c,hc⟩ := ih (b/3-1) hchild (a+1) hbound
        exact ⟨x,c,by simpa [hc]⟩
      · simp only [if_neg hr0] at hs ⊢
        by_cases hr1 : b%3=1
        · simp only [if_pos hr1] at hs ⊢
          have ha : a≠0 := by omega
          simp only [if_neg ha]
          have hchild : b/3 < b := by omega
          have hbound : safeBudget (b/3) ≤ a-1 := by omega
          obtain ⟨x,c,hc⟩ := ih (b/3) hchild (a-1) hbound
          exact ⟨x,c+4,by simpa [hc]⟩
        · simp only [if_neg hr1] at hs ⊢
          have ha : a≠0 := by omega
          simp only [if_neg ha]
          have hchild : b/3+1 < b := by omega
          have hbound : safeBudget (b/3+1) ≤ a-1 := by omega
          obtain ⟨x,c,hc⟩ := ih (b/3+1) hchild (a-1) hbound
          exact ⟨x,c+2,by simpa [hc]⟩

/-- New source-connected all-input survival region, with a threshold
computed from the actual base-three carry path of b. -/
theorem drainB_safeBudget (a b d : Nat) (hs : safeBudget b ≤ a) :
    ∃ x dd, drainB a b d = some (.D x dd) := by
  obtain ⟨x,c,hc⟩ := safeBudget_suffices b a hs
  refine ⟨x,d+3*b+c,?_⟩
  rw [drainB_digitCode]
  simp [hc,realize]

/-- Genuine ninefold arithmetic self-similarity of the safety budget. -/
theorem safeBudget_nine_pump (b : Nat) :
    safeBudget (9*b+6) = safeBudget b := by
  conv => lhs; rw [safeBudget]
  have hn : 9*b+6 ≠ 0 := by omega
  have hm : (9*b+6)%3=0 := by omega
  simp only [if_neg hn,if_pos hm]
  have hp : (9*b+6)/3-1=3*b+1 := by omega
  rw [hp,safeBudget]
  have hn1 : 3*b+1≠0 := by omega
  have hm0 : (3*b+1)%3≠0 := by omega
  have hm1 : (3*b+1)%3=1 := by omega
  simp only [if_neg hn1, if_neg hm0, if_pos hm1]
  have hdiv : (3*b+1)/3=b := by omega
  rw [hdiv]
  omega


/-- Exact ninefold compression of two complete B-drain reduction steps. -/
theorem flatB_nine_pump (a b d : Nat) :
    flatB a (9*b+6) d = flatB a b (d+24*b+22) := by
  conv => lhs; rw [flatB]
  have hn : 9*b+6 ≠ 0 := by omega
  have hm : (9*b+6)%3=0 := by omega
  simp only [if_neg hn, if_pos hm]
  have hb : (9*b+6)/3-1=3*b+1 := by omega
  rw [hb]
  conv => lhs; rw [flatB]
  have hn1 : 3*b+1≠0 := by omega
  have hm0 : (3*b+1)%3≠0 := by omega
  have hm1 : (3*b+1)%3=1 := by omega
  simp only [if_neg hn1,if_neg hm0,if_pos hm1]
  have ha1 : a+1≠0 := by omega
  simp only [if_neg ha1]
  have hd : (3*b+1)/3=b := by omega
  rw [hd]
  congr 1 <;> omega

/-- The exact same ninefold identity for the original, unmodified drainB. -/
theorem drainB_nine_pump (a b d : Nat) :
    drainB a (9*b+6) d = drainB a b (d+24*b+22) := by
  calc
    drainB a (9*b+6) d = flatB a (9*b+6) d :=
      (flatB_eq_drainB (9*b+6) a d).symm
    _ = flatB a b (d+24*b+22) := flatB_nine_pump a b d
    _ = drainB a b (d+24*b+22) :=
      flatB_eq_drainB b a (d+24*b+22)

/-- Exponentially increasing ternary block cylinders preserving budget zero. -/
def pumpBlock : Nat → Nat
  | 0 => 0
  | k+1 => 9*pumpBlock k+6

theorem pumpBlock_budget_zero (k : Nat) :
    safeBudget (pumpBlock k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change safeBudget (9*pumpBlock k+6)=0
    rw [safeBudget_nine_pump]
    exact ih

theorem pumpBlock_linear_growth (k : Nat) :
    6*k ≤ pumpBlock k := by
  induction k with
  | zero => simp [pumpBlock]
  | succ k ih =>
    simp only [pumpBlock]
    omega

/-- Source-authentic infinite family of successful drains with initial
first counter zero. The exact excess is 4k and b grows exponentially. -/
theorem pumpBlock_drain (k d : Nat) :
    drainB 0 (pumpBlock k) d =
      some (.D 0 (d+3*pumpBlock k+4*k)) := by
  induction k generalizing d with
  | zero => simp [pumpBlock,drainB]
  | succ k ih =>
    simp only [pumpBlock]
    rw [drainB_nine_pump, ih]
    simp only [Option.some.injEq, HighLevelState.D.injEq, true_and]
    omega

#print axioms flatB_nine_pump
#print axioms drainB_nine_pump
#print axioms pumpBlock_budget_zero
#print axioms pumpBlock_linear_growth
#print axioms pumpBlock_drain

#print axioms safeBudget_suffices
#print axioms drainB_safeBudget
#print axioms safeBudget_nine_pump
end BB6.Agent8SafeBudgetSource
