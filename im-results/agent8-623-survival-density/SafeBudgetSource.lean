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
  | zero => simp [pumpBlock,safeBudget]
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


theorem pumpBlock_even (k : Nat) : pumpBlock k%2=0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pumpBlock]
    omega

/-- An explicit infinite family of safe two-return escapes across the
exceptional a=d+2 diagonal of the authentic high-level machine. -/
theorem diagonal_escape (k : Nat) :
    let b := pumpBlock (k+1)
    (highLevelNext (.D b (b-2))).bind highLevelNext =
      some (.D (2+3*b+4*(k+1)) 7) := by
  intro b
  have hb : 6 ≤ b := by
    dsimp [b]
    have h := pumpBlock_linear_growth (k+1)
    omega
  have he : b%2=0 := pumpBlock_even (k+1)
  have hd : (b-2)%2=0 := by omega
  have hdiag : b=b-2+2 := by omega
  have hz : b≠0 := by omega
  have h1 : ¬ ((b-2)%2=1 ∧ b≥b-2+5) := by omega
  have h2 : ¬ ((b-2)%2=0 ∧ b≥b-2+3) := by omega
  have hpar : b%2≠1 := by omega
  have hstep : highLevelNext (.D b (b-2)) = drainB 0 b 2 := by
    simp only [highLevelNext,if_neg hz,if_neg h1,if_neg h2,if_neg hpar,if_pos hdiag]
  rw [hstep]
  have hp : drainB 0 b 2 = some (.D 0 (2+3*b+4*(k+1))) := by
    dsimp [b]
    exact pumpBlock_drain (k+1) 2
  rw [hp]
  have hs : (2+3*b+4*(k+1))%2=0 := by omega
  simp [highLevelNext,hs]

#print axioms pumpBlock_even
#print axioms diagonal_escape

#print axioms flatB_nine_pump
#print axioms drainB_nine_pump
#print axioms pumpBlock_budget_zero
#print axioms pumpBlock_linear_growth
#print axioms pumpBlock_drain


/-- Exact affine horizontal ray starting at the input-specific threshold.
The entire digit charge stays unchanged as the first counter increases. -/
theorem digitCode_safe_shift (b : Nat) :
  ∀ a t : Nat, safeBudget b ≤ a →
    digitCode (a+t) b = (digitCode a b).map (fun p => (p.1+t,p.2)) := by
  induction b using Nat.strongRecOn with
  | ind b ih =>
    intro a t hs
    rw [safeBudget] at hs
    conv => lhs; rw [digitCode]
    conv => rhs; arg 2; rw [digitCode]
    by_cases hz : b=0
    · simp [hz]
    · simp only [if_neg hz] at hs ⊢
      have hdiv : b=3*(b/3)+b%3 := by omega
      by_cases hr0 : b%3=0
      · simp only [if_pos hr0] at hs ⊢
        have hchild : b/3-1<b := by omega
        have hb : safeBudget (b/3-1) ≤ a+1 := by omega
        have hi := ih (b/3-1) hchild (a+1) t hb
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hi
      · simp only [if_neg hr0] at hs ⊢
        by_cases hr1 : b%3=1
        · simp only [if_pos hr1] at hs ⊢
          have ha : a≠0 := by omega
          have hat : a+t≠0 := by omega
          simp only [if_neg ha,if_neg hat]
          have hsChild : b/3<b := by omega
          have hb : safeBudget (b/3) ≤ a-1 := by omega
          have hshift : a+t-1=(a-1)+t := by omega
          rw [hshift,ih (b/3) hsChild (a-1) t hb]
          cases hc : digitCode (a-1) (b/3) with
          | none => simp [hc]
          | some p => rcases p with ⟨x,c⟩; simp [hc]
        · simp only [if_neg hr1] at hs ⊢
          have ha : a≠0 := by omega
          have hat : a+t≠0 := by omega
          simp only [if_neg ha,if_neg hat]
          have hsChild : b/3+1<b := by omega
          have hb : safeBudget (b/3+1) ≤ a-1 := by omega
          have hshift : a+t-1=(a-1)+t := by omega
          rw [hshift,ih (b/3+1) hsChild (a-1) t hb]
          cases hc : digitCode (a-1) (b/3+1) with
          | none => simp [hc]
          | some p => rcases p with ⟨x,c⟩; simp [hc]

/-- Genuine original-source drain transport, valid from the much tighter
per-block budget rather than a coarse uniform ternary-ones bound. -/
theorem drainB_safe_shift (a b d t : Nat) (hs : safeBudget b ≤ a) :
    drainB (a+t) b d = (drainB a b d).map
      (fun s => match s with | .D x dd => .D (x+t) dd) := by
  rw [drainB_digitCode,drainB_digitCode,digitCode_safe_shift b a t hs]
  cases hc : digitCode a b with
  | none => simp [hc]
  | some p =>
    rcases p with ⟨x,c⟩
    simp [hc,realize]


/-- A second, distinct two-digit pump. Unlike the +6 pump,
the zero-suffix pump requires a strictly positive input block count. -/
theorem safeBudget_nine_zero (b : Nat) (hb : 0<b) :
    safeBudget (9*b) = safeBudget b := by
  conv => lhs; rw [safeBudget]
  have hn : 9*b≠0 := by omega
  have hm : (9*b)%3=0 := by omega
  simp only [if_neg hn,if_pos hm]
  have hp : (9*b)/3-1=3*b-1 := by omega
  rw [hp,safeBudget]
  have hn1 : 3*b-1≠0 := by omega
  have hm0 : (3*b-1)%3≠0 := by omega
  have hm1 : (3*b-1)%3≠1 := by omega
  simp only [if_neg hn1,if_neg hm0,if_neg hm1]
  have hdiv : (3*b-1)/3+1=b := by omega
  rw [hdiv]
  omega

theorem flatB_nine_zero (a b d : Nat) (hb : 0<b) :
    flatB a (9*b) d = flatB a b (d+24*b+2) := by
  conv => lhs; rw [flatB]
  have hn : 9*b≠0 := by omega
  have hm : (9*b)%3=0 := by omega
  simp only [if_neg hn,if_pos hm]
  have hp : (9*b)/3-1=3*b-1 := by omega
  rw [hp]
  conv => lhs; rw [flatB]
  have hn1 : 3*b-1≠0 := by omega
  have hm0 : (3*b-1)%3≠0 := by omega
  have hm1 : (3*b-1)%3≠1 := by omega
  simp only [if_neg hn1,if_neg hm0,if_neg hm1]
  have ha1 : a+1≠0 := by omega
  simp only [if_neg ha1]
  have hd : (3*b-1)/3+1=b := by omega
  rw [hd]
  congr 1 <;> omega

theorem drainB_nine_zero (a b d : Nat) (hb : 0<b) :
    drainB a (9*b) d = drainB a b (d+24*b+2) := by
  calc
    drainB a (9*b) d = flatB a (9*b) d :=
      (flatB_eq_drainB (9*b) a d).symm
    _ = flatB a b (d+24*b+2) := flatB_nine_zero a b d hb
    _ = drainB a b (d+24*b+2) :=
      flatB_eq_drainB b a (d+24*b+2)

#print axioms safeBudget_nine_zero
#print axioms flatB_nine_zero
#print axioms drainB_nine_zero

#print axioms digitCode_safe_shift
#print axioms drainB_safe_shift

#print axioms safeBudget_suffices
#print axioms drainB_safeBudget
#print axioms safeBudget_nine_pump
end BB6.Agent8SafeBudgetSource
