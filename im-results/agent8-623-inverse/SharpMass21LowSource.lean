import Agent8SharpMass14OddSource
import Agent8RootedMass19Source
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem small_even_escape_seven (a d aa dd : Nat)
    (ha : a%2=0) (hsmall : a≤4) (hmass : 16≤a+d)
    (hstep : next (.D a d) = some (.D aa dd)) : 6≤aa ∧ 7≤dd := by
  have hcases : a=0 ∨ a=2 ∨ a=4 := by omega
  rcases hcases with h0 | h2 | h4
  · subst a
    simp only [next,highLevelNext, if_pos rfl] at hstep
    by_cases hd : d%2=1
    · simp only [if_pos hd] at hstep
      rw [drain_two_exact (d+1) (by omega)] at hstep
      cases hstep
      omega
    · simp only [if_neg hd] at hstep
      cases hstep
      omega
  · subst a
    simp only [next,highLevelNext, if_neg (by decide : (2:Nat)≠0)] at hstep
    have hs1 : ¬ (d%2=1 ∧ (2:Nat)≥d+5) := by omega
    have hs2 : ¬ (d%2=0 ∧ (2:Nat)≥d+3) := by omega
    simp only [if_neg hs1, if_neg hs2, if_neg (by decide : (2:Nat)%2≠1)] at hstep
    by_cases hd : d%2=1
    · have heq : 2 ≠ d+2 := by omega
      simp only [if_neg heq, if_pos hd] at hstep
      have harg : d+4-2=d+2 := by omega
      simp only [harg,Nat.reduceSub] at hstep
      rw [drain_one_exact (d+2) (by omega)] at hstep
      cases hstep
      omega
    · have heq : 2 ≠ d+2 := by omega
      simp only [if_neg heq, if_neg hd] at hstep
      have he : evalA (d+1-2) 2 (2*2+5) = some (d,0,9) := by
        rw [evalA]
        simp only [if_pos (by decide : 2%3=2)]
        simp only [if_true, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,Option.some.injEq,Prod.mk.injEq,true_and,and_true]
        omega
      rw [he] at hstep
      simp only [Option.bind_some] at hstep
      rw [drainB] at hstep
      simp only [if_pos (by decide : (0:Nat)=0)] at hstep
      cases hstep
      omega
  · subst a
    simp only [next,highLevelNext, if_neg (by decide : (4:Nat)≠0)] at hstep
    have hs1 : ¬ (d%2=1 ∧ (4:Nat)≥d+5) := by omega
    have hs2 : ¬ (d%2=0 ∧ (4:Nat)≥d+3) := by omega
    have heq : 4 ≠ d+2 := by omega
    simp only [if_neg hs1, if_neg hs2, if_neg (by decide : (4:Nat)%2≠1), if_neg heq] at hstep
    by_cases hd : d%2=1
    · simp only [if_pos hd] at hstep
      have heq2 : d+4-4=d := by omega
      rw [heq2,drain_three_exact] at hstep
      cases hstep
      omega
    · simp only [if_neg hd] at hstep
      have heq2 : d+1-4=d-3 := by omega
      rw [heq2, eval_four_exact (d-3) 13 (by omega)] at hstep
      simp only [Option.bind_some] at hstep
      rw [drainB] at hstep
      simp only [if_pos (by decide : (0:Nat)=0)] at hstep
      cases hstep
      omega

/-- The zero-second-counter ray immediately escapes to positive second counter. -/

#print axioms small_even_escape_seven
end BB6.Agent8SharpSource
