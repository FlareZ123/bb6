import RootMassGapAllN10
import Agent49DrainLinearLogSource
import Agent8DrainQuadraticLogSource
import Lean.Elab.Tactic.Omega

/-!
# Source output-depth bound for a scale-10 root transition

For a genuine blank-root state q whose minimum coordinate lies in the n=10
scale band, every successful source transition q→p has
p₂ ≤ 3*min(q₁,q₂)+69. The even gap-two source branch is excluded by the
already-developed root mass bracket.
-/

namespace BB6.Agent48SuccessorSecondBoundN10

open BusyBeaver
open BB6.Agent49ParitySource
open BB6.Agent49DrainLinearLogSource
open BB6.Agent8DrainQuadraticLogSource
open BB6.Agent8RootMassGapAllN10

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- A successful one-step root transition at scale 10 has the stated
linear bound on its second output coordinate. -/
theorem successor_second_bound_n10
    (t u v x y : Nat)
    (hseen : run t = some (.D u v))
    (hstep : highLevelNext (.D u v) = some (.D x y))
    (hmLo : 19680 <= min u v)
    (hmHi : min u v <= 59045) :
    y <= 3*min u v+69 := by
  have huEven : u % 2 = 0 := run_preserves_even t u v hseen
  have huPos : 0 < u := by omega
  have h0 : u ≠ 0 := by omega

  by_cases hvOdd : v % 2 = 1
  · by_cases hfar : v+5 <= u
    · have hDrain : drainB (u-v-5) (v+3) 5 = some (.D x y) := by
        have hred := hstep
        simp only [highLevelNext] at hred
        have h1 : v % 2 = 1 ∧ u >= v+5 := ⟨hvOdd, by omega⟩
        simp only [if_neg h0, if_pos h1] at hred
        exact hred
      have hblock : v+3 < 3^10 := by
        have hmin : min u v = v := by omega
        have hvBound : v <= 59045 := by simpa [hmin] using hmHi
        norm_num
        omega
      have hy := drainB_upper_linear_log 10 (u-v-5) (v+3) 5 x y hblock hDrain
      have hmin : min u v = v := by omega
      omega
    · have hnear : u <= v+4 := by omega
      have hDrain : drainB (v+4-u) (u-1) 3 = some (.D x y) := by
        have hred := hstep
        simp only [highLevelNext] at hred
        have h1 : ¬ (v % 2 = 1 ∧ u >= v+5) := by simp [hvOdd, hfar]
        have h2 : ¬ (v % 2 = 0 ∧ u >= v+3) := by simp [hvOdd]
        have h3 : ¬ (u % 2 = 1) := by simp [huEven]
        have h4 : u ≠ v+2 := by omega
        simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3,
          if_neg h4, if_pos hvOdd] at hred
        exact hred
      have huMin : u <= min u v+4 := by
        by_cases huv : u <= v
        · simp [min_eq_left huv]
        · have hvu : v <= u := by omega
          simp [min_eq_right hvu]
          omega
      have huBound : u <= 59049 := by
        by_cases huv : u <= v
        · have hmin : min u v = u := by simp [min_eq_left huv]
          have := hmHi
          simpa [hmin] using this
        · have hvu : v <= u := by omega
          have hmin : min u v = v := by simp [min_eq_right hvu]
          have hvBound : v <= 59045 := by simpa [hmin] using hmHi
          omega
      have hblock : u-1 < 3^10 := by norm_num; omega
      have hy := drainB_upper_linear_log 10 (v+4-u) (u-1) 3 x y hblock hDrain
      omega
  · have hvEven : v % 2 = 0 := by omega
    by_cases hfar : v+3 <= u
    · have hDrain : drainB (u-v-2) (v+2) 2 = some (.D x y) := by
        have hred := hstep
        simp only [highLevelNext] at hred
        have h1 : ¬ (v % 2 = 1 ∧ u >= v+5) := by simp [hvEven]
        have h2 : v % 2 = 0 ∧ u >= v+3 := ⟨hvEven, by omega⟩
        simp only [if_neg h0, if_neg h1, if_pos h2] at hred
        exact hred
      have hblock : v+2 < 3^10 := by
        have hmin : min u v = v := by omega
        have hvBound : v <= 59045 := by simpa [hmin] using hmHi
        norm_num
        omega
      have hy := drainB_upper_linear_log 10 (u-v-2) (v+2) 2 x y hblock hDrain
      have hmin : min u v = v := by omega
      omega
    · by_cases hgap : u = v+2
      · have hmin : min u v = v := by omega
        have hvLo : 19680 <= v := by simpa [hmin] using hmLo
        have hvHi : v <= 59045 := by simpa [hmin] using hmHi
        have hseenGap : run t = some (.D (v+2) v) := by simpa [hgap] using hseen
        exact (n10_even_gap_two_root_excluded t v hseenGap hvLo hvHi).elim
      · have hnear : u <= v := by omega
        have hmin : min u v = u := by simp [min_eq_left hnear]
        have huBound : u <= 59045 := by simpa [hmin] using hmHi
        have hUk : u < 3^10 := by norm_num; omega
        have hEvalDrain :
            (evalA (v+1-u) u (2*u+5)).bind
              (fun z => match z with
                | (p,q,r) => drainB p q r) = some (.D x y) := by
          have hred := hstep
          simp only [highLevelNext] at hred
          have h1 : ¬ (v % 2 = 1 ∧ u >= v+5) := by simp [hvEven]
          have h2 : ¬ (v % 2 = 0 ∧ u >= v+3) := by simp [hvEven, hfar]
          have h3 : ¬ (u % 2 = 1) := by simp [huEven]
          have h4 : u ≠ v+2 := hgap
          have h5 : ¬ (v % 2 = 1) := by omega
          simp only [if_neg h0, if_neg h1, if_neg h2, if_neg h3,
            if_neg h4, if_neg h5] at hred
          exact hred
        simp only [Option.bind_eq_some_iff] at hEvalDrain
        rcases hEvalDrain with ⟨⟨p,q,r⟩, hEval, hDrain⟩
        have hqBound : q < 3^10 := by
          by_cases hq0 : q = 0
          · simp [hq0]
          · have hdepth :=
              evalA_positive_depth 10 (v+1-u) u (2*u+5) p q r
                hUk (by omega) hEval
            rcases hdepth with ⟨r0,s0,hrs,hrpos,hqSmall,_,_⟩
            have hsBound : s0 <= 10 := by omega
            have hpow : 3^s0 <= 3^10 :=
              Nat.pow_le_pow_right (by omega) hsBound
            omega
        have hEvalUpper :=
          evalA_upper_log 10 (v+1-u) u (2*u+5) p q r hUk hEval
        have hDrainUpper :=
          drainB_upper_linear_log 10 p q r x y hqBound hDrain
        omega

#print axioms successor_second_bound_n10

end BB6.Agent48SuccessorSecondBoundN10


/-- Advance the genuine blank-root run by one source transition. -/
theorem run_succ_of_highLevelNext
    (t u v x y : Nat)
    (hseen : run t = some (.D u v))
    (hstep : highLevelNext (.D u v) = some (.D x y)) :
    run (t+1) = some (.D x y) := by
  simp only [run, hseen, Option.bind_some]
  exact hstep

#print axioms run_succ_of_highLevelNext
