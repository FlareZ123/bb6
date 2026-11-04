import Agent8RootedMassSource

/-!
Exact one-return formulas for the three small even first-counter families in
Cryptids #623, with high second counter. Uses the unchanged original
highLevelNext and Agent 8's source-proven drain primitives. These statements
are not blank-reachability claims.
-/

namespace BB6.Agent49LowStepSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8SharpSource

theorem low_zero_even (d : Nat) (hd : d%2=0) :
    highLevelNext (.D 0 d)=some (.D d 7) := by
  simp [highLevelNext,hd]

theorem low_zero_odd (d : Nat) (hd : d%2=1) (hbig : 2≤d) :
    highLevelNext (.D 0 d)=some (.D (d-1) 14) := by
  simp only [highLevelNext,if_pos (rfl : (0:Nat)=0),if_pos hd]
  rw [drain_two_exact (d+1) (by omega)]
  congr 1 <;> omega

theorem low_two_even (d : Nat) (hd : d%2=0) (hbig : 10≤d) :
    highLevelNext (.D 2 d)=some (.D d 9) := by
  simp only [highLevelNext,if_neg (by decide : (2:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (2:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (2:Nat)≥d+3) := by omega
  have h4 : 2 ≠ d+2 := by omega
  have hnotodd : d%2 ≠ 1 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (2:Nat)%2≠1),
    if_neg h4,if_neg hnotodd]
  have he : evalA (d+1-2) 2 (2*2+5) = some (d,0,9) := by
    rw [evalA]
    simp only [if_pos (by decide : 2%3=2)]
    simp only [if_true,Nat.reduceDiv,Nat.reduceMul,Nat.reduceAdd,
      Option.some.injEq,Prod.mk.injEq,true_and,and_true]
    omega
  rw [he]
  simp only [Option.bind_some]
  rw [drainB]
  simp only [if_pos (by decide : (0:Nat)=0)]
  rfl

theorem low_two_odd (d : Nat) (hd : d%2=1) (hbig : 10≤d) :
    highLevelNext (.D 2 d)=some (.D (d+1) 10) := by
  simp only [highLevelNext,if_neg (by decide : (2:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (2:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (2:Nat)≥d+3) := by omega
  have h4 : 2 ≠ d+2 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (2:Nat)%2≠1),
    if_neg h4,if_pos hd]
  have heq : d+4-2=d+2 := by omega
  rw [heq,drain_one_exact (d+2) (by omega)]
  congr 1 <;> omega

theorem low_four_even (d : Nat) (hd : d%2=0) (hbig : 16≤d) :
    highLevelNext (.D 4 d)=some (.D (d-6) 23) := by
  simp only [highLevelNext,if_neg (by decide : (4:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (4:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (4:Nat)≥d+3) := by omega
  have h4 : 4 ≠ d+2 := by omega
  have hnotodd : d%2 ≠ 1 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (4:Nat)%2≠1),
    if_neg h4,if_neg hnotodd]
  have heq : d+1-4=d-3 := by omega
  rw [heq,eval_four_exact (d-3) 13 (by omega)]
  simp only [Option.bind_some]
  rw [drainB]
  congr 1 <;> omega

theorem low_four_odd (d : Nat) (hd : d%2=1) (hbig : 16≤d) :
    highLevelNext (.D 4 d)=some (.D (d+1) 12) := by
  simp only [highLevelNext,if_neg (by decide : (4:Nat)≠0)]
  have h1 : ¬ (d%2=1 ∧ (4:Nat)≥d+5) := by omega
  have h2 : ¬ (d%2=0 ∧ (4:Nat)≥d+3) := by omega
  have h4 : 4 ≠ d+2 := by omega
  simp only [if_neg h1,if_neg h2,if_neg (by decide : (4:Nat)%2≠1),
    if_neg h4,if_pos hd]
  have heq : d+4-4=d := by omega
  rw [heq,drain_three_exact]

#print axioms low_zero_even
#print axioms low_zero_odd
#print axioms low_two_even
#print axioms low_two_odd
#print axioms low_four_even
#print axioms low_four_odd
end BB6.Agent49LowStepSource
