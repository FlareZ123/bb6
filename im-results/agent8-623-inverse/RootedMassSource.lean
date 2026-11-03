import Agent8SharpMass10Source

/-! Theorems about low first-counter escape and real blank-origin two-step growth
for Cryptid #623. Imports unmodified upstream source via mass modules.
-/
namespace BB6.Agent8SharpSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
private abbrev next : HighLevelState → Option HighLevelState := highLevelNext

theorem drain_two_exact (a : Nat) (ha : 2 ≤ a) :
    drainB a 2 2 = some (.D (a-2) 14) := by
  rw [drainB]
  simp only [if_neg (by decide : (2:Nat)≠0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  have he : evalA a 1 9 = some (a-2,0,14) := by
    rw [evalA]
    simp only [if_neg (by decide : 1%3≠2), if_neg (by omega : a≠0),
      if_neg (by decide : 1%3≠0)]
    have ha1 : a-1 ≠ 0 := by omega
    rw [evalA]
    simp only [if_neg (by decide : 0%3≠2), if_neg ha1,
      if_pos (by decide : 0%3=0)]
    congr 1 <;> omega
  rw [he]
  simp only [Option.bind_some, if_pos (by decide : (0:Nat)<2)]
  rw [drainB]
  simp only [if_pos (by decide : (0:Nat)=0)]
  rfl

theorem drain_one_exact (a : Nat) (ha : 1 ≤ a) :
    drainB a 1 3 = some (.D (a-1) 10) := by
  rw [drainB]
  simp only [if_neg (by decide : (1:Nat)≠0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  rw [evalA]
  simp only [if_neg (by decide : 0%3≠2), if_neg (by omega : a≠0),
    if_pos (by decide : 0%3=0)]
  simp only [if_true, Nat.reduceDiv, Option.bind_some, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT]
  rw [drainB]
  simp only [if_pos (by decide : (0:Nat)=0)]
  rfl

theorem drain_three_exact (a : Nat) :
    drainB a 3 3 = some (.D (a+1) 12) := by
  rw [drainB]
  simp only [if_neg (by decide : (3:Nat)≠0), Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  rw [evalA]
  simp only [if_pos (by decide : 2%3=2)]
  simp only [if_true, Nat.reduceDiv, Option.bind_some, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT]
  rw [drainB]
  simp only [if_pos (by decide : (0:Nat)=0)]
  rfl

theorem eval_four_exact (a m : Nat) (ha : 3 ≤ a) :
    evalA a 4 m = some (a-3,0,m+10) := by
  rw [evalA]
  simp only [if_neg (by decide : 4%3≠2), if_neg (by omega : a ≠ 0),
    if_neg (by decide : 4%3≠0)]
  have ha1 : a-1 ≠ 0 := by omega
  rw [evalA]
  simp only [if_neg (by decide : 1%3≠2), if_neg ha1,
    if_neg (by decide : 1%3≠0)]
  have ha2 : a-2 ≠ 0 := by omega
  rw [evalA]
  simp only [if_neg (by decide : 0%3≠2), if_neg ha2,
    if_pos (by decide : 0%3=0)]
  have hn : a-1-1 ≠ 0 := by omega
  simp only [if_neg hn, if_true, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd]
  simp only [Option.some.injEq,Prod.mk.injEq,true_and,and_true]
  omega

/-- Every successful high-mass transition with small even a escapes
to a first counter at least six. -/
theorem small_even_escape (a d aa dd : Nat)
    (ha : a%2=0) (hsmall : a≤4) (hmass : 16≤a+d)
    (hstep : next (.D a d) = some (.D aa dd)) : 6≤aa := by
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
        simp only [if_true, Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd,
          Option.some.injEq,Prod.mk.injEq,true_and,and_true]
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

/-- Above mass 16, every two successful steps with even first counters
gain at least seventeen total units. -/
theorem two_step_gain_17 (a d b e c f : Nat)
    (ha : a%2=0) (hb : b%2=0) (hmass : 16≤a+d)
    (h1 : next (.D a d) = some (.D b e))
    (h2 : next (.D b e) = some (.D c f))
    (h7first : a+d+7≤b+e) (h7second : b+e+7≤c+f) :
    a+d+17≤c+f := by
  by_cases hhigh : 6≤a
  · have h10 := next_even_six_mass a d b e ha hhigh h1
    omega
  · have hsmall : a≤4 := by omega
    have hesc := small_even_escape a d b e ha hsmall hmass h1
    have h10 := next_even_six_mass b e c f hb hesc h2
    omega

/-- The actual blank-start accelerated orbit gains at least seventeen
counter units on each surviving pair of returns after index two. -/
theorem root_two_step_gain_17 (n a d c f : Nat)
    (hn : 2 ≤ n)
    (hbefore : run n = some (.D a d))
    (hafter : run (n+2) = some (.D c f)) :
    a+d+17 ≤ c+f := by
  have hbig : 16 ≤ a+d := by
    have h := run_grows_at_least_seven n a d hbefore
    omega
  have heven := run_preserves_even n a d hbefore
  cases hmid : next (.D a d) with
  | none =>
    have hm : run (n+1) = none := by
      change (run n).bind highLevelNext = none
      rw [hbefore]
      exact hmid
    have hz : run (n+2) = none := by
      change (run (n+1)).bind highLevelNext = none
      rw [hm]
      rfl
    simp [hz] at hafter
  | some s =>
    rcases s with ⟨b,e⟩
    have hmidrun : run (n+1) = some (.D b e) := by
      change (run n).bind highLevelNext = some (.D b e)
      rw [hbefore]
      exact hmid
    have hstep2 : next (.D b e) = some (.D c f) := by
      change (run (n+1)).bind highLevelNext = some (.D c f) at hafter
      rw [hmidrun] at hafter
      exact hafter
    have heven2 := run_preserves_even (n+1) b e hmidrun
    have h7a := next_strict_mass a d b e hmid
    have h7b := next_strict_mass b e c f hstep2
    exact two_step_gain_17 a d b e c f heven heven2 hbig hmid hstep2 h7a h7b

#print axioms small_even_escape
#print axioms two_step_gain_17
#print axioms root_two_step_gain_17
end BB6.Agent8SharpSource
