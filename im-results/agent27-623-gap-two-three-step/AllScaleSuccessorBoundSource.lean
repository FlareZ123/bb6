import Agent8RootCorridorSource
import Agent49DrainLinearLogSource
import Lean.Elab.Tactic.Omega

namespace BB6.Agent27AllScaleSuccessorBoundSource

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent8DrainQuadraticLogSource
open BB6.Agent8DrainLogDepthSource
open BB6.Agent8ZeroTailSource
open BB6.Agent8RootCorridorSource

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- A uniform upper bound for every successful even-first-counter step,
including both exceptional branches. -/
theorem successor_second_bound (n u v x y : Nat)
    (hn : 4 ≤ n) (hdepth : min u v+3 < 3^n) (huEven : u%2=0)
    (hstep : highLevelNext (.D u v) = some (.D x y)) :
    y ≤ 3*min u v+6*n+9 := by
  by_cases h0 : u=0
  · subst u
    by_cases ho : v%2=1
    · rw [zero_odd_source v ho] at hstep
      cases hstep
      omega
    · have he : v%2=0 := by omega
      rw [zero_even_source v he] at hstep
      cases hstep
      omega
  · by_cases ho : v%2=1
    · by_cases hf : v+5≤u
      · have h1 : v%2=1 ∧ u≥v+5 := ⟨ho,hf⟩
        simp only [highLevelNext,if_neg h0,if_pos h1] at hstep
        have hm : min u v=v := by omega
        have hb : v+3<3^n := by omega
        have hy := drainB_upper_linear_log n (u-v-5) (v+3) 5 x y hb hstep
        omega
      · have h1 : ¬(v%2=1 ∧ u≥v+5) := by omega
        have h2 : ¬(v%2=0 ∧ u≥v+3) := by omega
        have h3 : u%2≠1 := by omega
        have h4 : u≠v+2 := by omega
        simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos ho] at hstep
        have hb : u-1<3^n := by omega
        have hy := drainB_upper_linear_log n (v+4-u) (u-1) 3 x y hb hstep
        omega
    · have he : v%2=0 := by omega
      by_cases hf : v+3≤u
      · have h1 : ¬(v%2=1 ∧ u≥v+5) := by omega
        have h2 : v%2=0 ∧ u≥v+3 := ⟨he,hf⟩
        simp only [highLevelNext,if_neg h0,if_neg h1,if_pos h2] at hstep
        have hb : v+2<3^n := by omega
        have hy := drainB_upper_linear_log n (u-v-2) (v+2) 2 x y hb hstep
        omega
      · have h1 : ¬(v%2=1 ∧ u≥v+5) := by omega
        have h2 : ¬(v%2=0 ∧ u≥v+3) := by omega
        have h3 : u%2≠1 := by omega
        by_cases hg : u=v+2
        · simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos hg] at hstep
          have hb : u<3^n := by omega
          have hy := drainB_upper_linear_log n 0 u 2 x y hb hstep
          omega
        · have huv : u≤v := by omega
          have hb : u<3^n := by omega
          simp only [highLevelNext,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg hg,if_neg ho] at hstep
          cases hev : evalA (v+1-u) u (2*u+5) with
          | none => simp [hev] at hstep
          | some p =>
            rcases p with ⟨a,b,d⟩
            simp only [hev,Option.bind_some] at hstep
            have hq := evalA_second_le_quotient (v+1-u) u (2*u+5) a b d hev
            have hblock : b<3^n := by omega
            have hEval := evalA_upper_log n (v+1-u) u (2*u+5) a b d hb hev
            have hDrain := drainB_upper_linear_log n a b d x y hblock hstep
            omega

/-- Source arithmetic reduces every putative third predecessor with small
minimum coordinate to a bounded mass. -/
theorem small_min_terminal_mass (t u v x y aa dd : Nat)
    (hq : run t = some (.D u v)) (hm : min u v ≤ 19679)
    (hs : highLevelNext (.D u v) = some (.D x y))
    (ht : highLevelNext (.D x y) = some (.D aa dd))
    (hh : highLevelNext (.D aa dd) = none) : u+v ≤ 1004761 := by
  have hdepth : min u v+3 < 3^9 := by
    have hp : 3^9=19683 := by decide
    omega
  have hy := successor_second_bound 9 u v x y (by decide) hdepth
    (run_preserves_even t u v hq) hs
  have hp : run (t+1) = some (.D x y) := by simpa [run,hq] using hs
  obtain ⟨hpos,hodd,heven,hgate⟩ :=
    blank_root_two_step_terminal_parent_corridor (t+1) x y aa dd hp ht hh
  have hx : x < 16*y+68 := by
    by_cases h : y%2=1
    · exact (hodd h).2
    · have h0 : y%2=0 := by omega
      have hb := (heven h0).2
      omega
  have hg := next_strict_mass u v x y hs
  omega

-- Native evaluation is an explicit trust dependency for these checkpoints.
theorem root_run_47_small_scale : run 47 = some (.D 145494 1278161) := by native_decide
theorem root_run_49_small_scale : run 49 = some (.D 696164 1309542) := by native_decide

theorem root_mass_after_47 (k a d : Nat)
    (h : run (47+k) = some (.D a d)) : 1423655 ≤ a+d := by
  induction k generalizing a d with
  | zero =>
      simp only [Nat.add_zero,root_run_47_small_scale] at h
      cases h
      decide
  | succ k ih =>
      have heq : 47+(k+1)=(47+k)+1 := by omega
      rw [heq,run] at h
      cases hr : run (47+k) with
      | none => simp [hr] at h
      | some s =>
          rcases s with ⟨x,y⟩
          simp only [hr,Option.bind_some] at h
          have hm := ih x y hr
          have hg := next_strict_mass x y a d h
          omega

theorem run_none_forward (t : Nat) (h : run t = none) (k : Nat) :
    run (t+k) = none := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
      change (run (t+k)).bind highLevelNext = none
      rw [ih]
      rfl

/-- No blank-root three-step terminal event has minimum coordinate below the
scale-10 band. This also removes the zero-first-counter branch at all times. -/
theorem blank_root_no_small_min_three_step_terminal
    (t u v x y aa dd : Nat)
    (hq : run t = some (.D u v)) (hm : min u v ≤ 19679)
    (hs : highLevelNext (.D u v) = some (.D x y))
    (ht : highLevelNext (.D x y) = some (.D aa dd))
    (hh : highLevelNext (.D aa dd) = none) : False := by
  have hmass := small_min_terminal_mass t u v x y aa dd hq hm hs ht hh
  have hlt : t<47 := by
    by_cases h : t<47
    · exact h
    · have heq : 47+(t-47)=t := by omega
      have hseen : run (47+(t-47)) = some (.D u v) := by rwa [heq]
      have hlo := root_mass_after_47 (t-47) u v hseen
      omega
  have hp : run (t+1) = some (.D x y) := by simpa [run,hq] using hs
  have hr : run (t+2) = some (.D aa dd) := by
    change (run (t+1)).bind highLevelNext = some (.D aa dd)
    rw [hp]
    exact ht
  have hn : run (t+3)=none := by
    change (run (t+2)).bind highLevelNext = none
    rw [hr]
    exact hh
  have h49 : run 49=none := by
    have heq : t+3+(49-(t+3))=49 := by omega
    have hz := run_none_forward (t+3) hn (49-(t+3))
    rwa [heq] at hz
  rw [root_run_49_small_scale] at h49
  contradiction

#print axioms successor_second_bound
#print axioms small_min_terminal_mass
#print axioms root_run_47_small_scale
#print axioms root_run_49_small_scale
#print axioms root_mass_after_47
#print axioms blank_root_no_small_min_three_step_terminal

end BB6.Agent27AllScaleSuccessorBoundSource
