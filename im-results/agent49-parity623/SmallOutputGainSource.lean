import Agent8BudgetSource
import Agent49WeightedSource

/-!
A source-attached gain bound for the small-first-counter image of the
unchanged Cryptids #623 accelerator. Statements concern successful steps;
no raw-machine halting conclusion follows.
-/

namespace BB6.Agent49SmallOutputSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem next_small_first_gain20 (a d b e : Nat)
    (ha : a%2=0) (ha6 : 6≤a) (hd : 0<d) (hm : 100≤a+d)
    (hb : b≤4) (hstep : next (.D a d)=some (.D b e)) :
    a+d+20 ≤ b+e := by
  simp only [next, highLevelNext] at hstep
  have h0 : a ≠ 0 := by omega
  simp only [if_neg h0] at hstep
  by_cases h1 : d%2=1 ∧ a≥d+5
  · simp only [if_pos h1] at hstep
    have hw := (BB6.Agent49WeightedSource.drainB_weight2
      (d+3) (a-d-5) 5 b e hstep).2 (by omega)
    have he := BB6.Agent8BudgetSource.drainB_d3 (d+3) (a-d-5) 5 b e hstep
    omega
  · simp only [if_neg h1] at hstep
    by_cases h2 : d%2=0 ∧ a≥d+3
    · simp only [if_pos h2] at hstep
      have hw := (BB6.Agent49WeightedSource.drainB_weight2
        (d+2) (a-d-2) 2 b e hstep).2 (by omega)
      have he := BB6.Agent8BudgetSource.drainB_d3 (d+2) (a-d-2) 2 b e hstep
      omega
    · simp only [if_neg h2] at hstep
      have hodd : a%2 ≠ 1 := by omega
      simp only [if_neg hodd] at hstep
      by_cases h4 : a=d+2
      · simp only [if_pos h4] at hstep
        have he := BB6.Agent8BudgetSource.drainB_d3 a 0 2 b e hstep
        omega
      · simp only [if_neg h4] at hstep
        by_cases h5 : d%2=1
        · simp only [if_pos h5] at hstep
          have hw := (BB6.Agent49WeightedSource.drainB_weight2
            (a-1) (d+4-a) 3 b e hstep).2 (by omega)
          have he := BB6.Agent8BudgetSource.drainB_d3 (a-1) (d+4-a) 3 b e hstep
          omega
        · simp only [if_neg h5] at hstep
          cases hev : evalA (d+1-a) a (2*a+5) with
          | none => simp [hev] at hstep
          | some p =>
            rcases p with ⟨a1,b1,d1⟩
            simp only [hev, Option.bind_some] at hstep
            have hw1 := BB6.Agent49WeightedSource.evalA_weight2
              (d+1-a) a (2*a+5) a1 b1 d1 hev
            have hw2 := (BB6.Agent49WeightedSource.drainB_weight2
              b1 a1 d1 b e hstep).1
            have hd1 := BB6.Agent8BudgetSource.evalA_ternary_budget
              (d+1-a) a (2*a+5) a1 b1 d1 hev
            have hd2 := BB6.Agent8BudgetSource.drainB_d3 b1 a1 d1 b e hstep
            omega

#print axioms next_small_first_gain20
/-- Every successful high-level transition has output second counter at least 2. -/
theorem next_output_second_two (a d b e : Nat)
    (hstep : next (.D a d)=some (.D b e)) : 2 ≤ e := by
  simp only [next, highLevelNext] at hstep
  by_cases h0 : a=0
  · simp only [if_pos h0] at hstep
    by_cases hdo : d%2=1
    · simp only [if_pos hdo] at hstep
      have he := BB6.Agent8BudgetSource.drainB_d3 2 (d+1) 2 b e hstep
      omega
    · simp only [if_neg hdo] at hstep
      cases hstep
      omega
  · simp only [if_neg h0] at hstep
    by_cases h1 : d%2=1 ∧ a≥d+5
    · simp only [if_pos h1] at hstep
      have he := BB6.Agent8BudgetSource.drainB_d3 (d+3) (a-d-5) 5 b e hstep
      omega
    · simp only [if_neg h1] at hstep
      by_cases h2 : d%2=0 ∧ a≥d+3
      · simp only [if_pos h2] at hstep
        have he := BB6.Agent8BudgetSource.drainB_d3 (d+2) (a-d-2) 2 b e hstep
        omega
      · simp only [if_neg h2] at hstep
        by_cases hodd : a%2=1
        · simp [hodd] at hstep
        · simp only [if_neg hodd] at hstep
          by_cases h4 : a=d+2
          · simp only [if_pos h4] at hstep
            have he := BB6.Agent8BudgetSource.drainB_d3 a 0 2 b e hstep
            omega
          · simp only [if_neg h4] at hstep
            by_cases h5 : d%2=1
            · simp only [if_pos h5] at hstep
              have he := BB6.Agent8BudgetSource.drainB_d3 (a-1) (d+4-a) 3 b e hstep
              omega
            · simp only [if_neg h5] at hstep
              cases hev : evalA (d+1-a) a (2*a+5) with
              | none => simp [hev] at hstep
              | some p =>
                rcases p with ⟨a1,b1,d1⟩
                simp only [hev,Option.bind_some] at hstep
                have hd1 := BB6.Agent8BudgetSource.evalA_ternary_budget
                  (d+1-a) a (2*a+5) a1 b1 d1 hev
                have hd2 := BB6.Agent8BudgetSource.drainB_d3 b1 a1 d1 b e hstep
                omega

#print axioms next_output_second_two

end BB6.Agent49SmallOutputSource
