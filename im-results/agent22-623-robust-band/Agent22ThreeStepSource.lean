import Agent8BudgetSource
import Agent49FlatDrainSource

/-!
An infinite original-Cryptids-source synthetic three-step halting family.
No assertion about the fixed blank-origin section D(0,7).
-/
namespace BB6.Agent22ThreeStepSource
open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent8BudgetSource
open BB6.Agent49FlatDrainSource

/-- This is the exact tight-block parameterization, duplicated locally to
avoid depending on unrelated synthetic-pole proof machinery. -/
def xFamily (m : Nat) : Nat := 3*tightB m+2

private theorem tightB_mod_two (m : Nat) : tightB m%2=m%2 := by
  induction m with
  | zero => simp [tightB]
  | succ m ih =>
      simp only [tightB]
      omega

private theorem xFamily_even (m : Nat) (hm : m%2=0) : xFamily m%2=0 := by
  have hb := tightB_mod_two m
  dsimp [xFamily]
  omega

private theorem tight_ge (m : Nat) : m ≤ tightB m := by
  induction m with
  | zero => simp [tightB]
  | succ m ih =>
      simp only [tightB]
      omega

private theorem x_ge (m : Nat) : 2*m ≤ xFamily m := by
  have h := tight_ge m
  dsimp [xFamily]
  omega

/-- Exact first return for a tuned right-even initial ray. -/
theorem first_tuned (m : Nat) (hm : m%2=0) :
    highLevelNext (.D (xFamily m) (13*xFamily m-2*m+32)) =
      some (.D (12*xFamily m-m+34) (3*xFamily m+3)) := by
  let x := xFamily m
  let d := 13*x-2*m+32
  have hxpos : 0<x := by dsimp [x,xFamily]; omega
  have hxeven : x%2=0 := by simpa only [x] using xFamily_even m hm
  have hxbound : 2*m≤x := by simpa only [x] using x_ge m
  have hdlarge : x+4≤d := by dsimp [d]; omega
  have hdeven : d%2=0 := by dsimp [d]; omega
  have hxmod : x%3=2 := by dsimp [x,xFamily]; omega
  have hxdiv : x/3=tightB m := by dsimp [x,xFamily]; omega
  have harg : (d+1-x)+1=d+2-x := by omega
  have heval :
      evalA (d+1-x) x (2*x+5) =
        some (d+2-x,tightB m,2*x+5) := by
    rw [evalA]
    simp only [if_pos hxmod,hxdiv,harg]
  have hfirst : d+2-x+m=12*x-m+34 := by dsimp [d]; omega
  have hthird : 2*x+5+3*tightB m=3*x+3 := by dsimp [x,xFamily]; omega
  have hdrain :
      drainB (d+2-x) (tightB m) (2*x+5) =
        some (.D (12*x-m+34) (3*x+3)) := by
    simpa only [hfirst,hthird] using drainB_tight m (d+2-x) (2*x+5)
  have h0 : x≠0 := by omega
  have h1 : ¬(d%2=1 ∧ x≥d+5) := by omega
  have h2 : ¬(d%2=0 ∧ x≥d+3) := by omega
  have h3 : x%2≠1 := by omega
  have h4 : x≠d+2 := by omega
  have h5 : d%2≠1 := by omega
  change highLevelNext (.D x d)=some (.D (12*x-m+34) (3*x+3))
  simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,
    if_neg h4,if_neg h5]
  rw [heval]
  simpa only [Option.bind_some] using hdrain

/-- The second return lands at a fixed five-unit left-ray gap. -/
theorem second_tuned (m : Nat) (hm : m%2=0) :
    highLevelNext (.D (12*xFamily m-m+34) (3*xFamily m+3)) =
      some (.D (9*xFamily m+28) (9*xFamily m+23)) := by
  let x := xFamily m
  let a := 12*x-m+34
  let d := 3*x+3
  have hxeven : x%2=0 := by simpa only [x] using xFamily_even m hm
  have hxbound : 2*m≤x := by simpa only [x] using x_ge m
  have hdodd : d%2=1 := by dsimp [d]; omega
  have hfar : d+5≤a := by dsimp [a,d]; omega
  have hblock : d+3=tightB (m+2) := by
    dsimp [d,x,xFamily]
    simp only [tightB]
    omega
  have hfirst : a-d-5+(m+2)=9*x+28 := by dsimp [a,d]; omega
  have hthird : 5+3*(d+3)=9*x+23 := by dsimp [d]; omega
  have hdrain :
      drainB (a-d-5) (d+3) 5 =
        some (.D (9*x+28) (9*x+23)) := by
    rw [hblock]
    have h := drainB_tight (m+2) (a-d-5) 5
    have hfirst' : a-d-5+(m+2)=9*x+28 := hfirst
    have hthird' : 5+3*tightB (m+2)=9*x+23 := by rw [←hblock]; exact hthird
    simpa only [hfirst',hthird'] using h
  have ha : a≠0 := by omega
  have hcond : d%2=1 ∧ a≥d+5 := ⟨hdodd,hfar⟩
  change highLevelNext (.D a d)=some (.D (9*x+28) (9*x+23))
  simpa only [highLevelNext,if_neg ha,if_pos hcond] using hdrain

/-- The final B-drain fails after three explicit low ternary digits. -/
theorem third_tuned (m : Nat) (hm : m%2=0) :
    highLevelNext (.D (9*xFamily m+28) (9*xFamily m+23)) = none := by
  let x := xFamily m
  let t := tightB m
  have hxeven : x%2=0 := by simpa only [x] using xFamily_even m hm
  have hdodd : (9*x+23)%2=1 := by omega
  have hfar : 9*x+23+5≤9*x+28 := by omega
  have hblock : 9*x+26=3*(9*t+14)+2 := by dsimp [x,xFamily,t]; omega
  have hsecond : 9*t+14=3*(3*t+4)+2 := by omega
  have hthird : 3*t+4=3*(t+1)+1 := by omega
  have hbad : drainB 0 (9*x+26) 5 = none := by
    rw [hblock]
    rw [drain_three_two_zero]
    rw [hsecond]
    rw [drain_three_two_zero]
    rw [hthird]
    exact drain_three_one_zero (t+1) _
  have ha : 9*x+28 ≠ 0 := by omega
  have hcond : (9*x+23)%2=1 ∧ 9*x+28≥9*x+23+5 := ⟨hdodd,hfar⟩
  have hfirstarg : 9*x+28-(9*x+23)-5=0 := by omega
  have hsecondarg : 9*x+23+3=9*x+26 := by omega
  change highLevelNext (.D (9*x+28) (9*x+23)) = none
  simpa only [highLevelNext,if_neg ha,if_pos hcond,hfirstarg,hsecondarg] using hbad

/-- All even parameters give an explicit three-return synthetic halt. -/
theorem three_step_synthetic_halts (m : Nat) (hm : m%2=0) :
    highLevelNext (.D (xFamily m) (13*xFamily m-2*m+32)) =
      some (.D (12*xFamily m-m+34) (3*xFamily m+3)) ∧
    highLevelNext (.D (12*xFamily m-m+34) (3*xFamily m+3)) =
      some (.D (9*xFamily m+28) (9*xFamily m+23)) ∧
    highLevelNext (.D (9*xFamily m+28) (9*xFamily m+23)) = none := by
  exact ⟨first_tuned m hm,second_tuned m hm,third_tuned m hm⟩

#print axioms three_step_synthetic_halts
end BB6.Agent22ThreeStepSource
