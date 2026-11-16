import Agent49ParitySource
import Agent8GateCompleteSource
import Agent8RootCancellationBudgetBridge
import Agent8RootCorridorSource
import Agent49TerminalRatio4Source
import Lean.Elab.Tactic.Omega

/-!
# Fixed-depth terminal ratio window for a genuine root parent

If a genuine root state p has a successful child h which halts immediately,
and p₂ ≤ 177204, then the terminal source lemmas apply uniformly at n=12,
K=15. The rooted angular corridor supplies the mass budget; the exceptional
even gap-two branch is ruled out by the corridor's no-gate conclusion.
This is an intermediate source-composition lemma, not a BB(6) result.
-/

namespace BB6.Agent48TerminalWindowAtDepth12

open BusyBeaver
open BB6.Agent49ParitySource
open BB6.Agent8GateCompleteSource
open BB6.Agent8RootCancellationBudgetBridge
open BB6.Agent8RootCorridorSource
open BB6.Agent49TerminalRatio4Source

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- A root terminal parent with a moderately bounded second coordinate
has a ratio-four window of width at most 128, at fixed depth 12 and
mass exponent 15. -/
theorem terminal_window_at_depth12
    (t x y aa dd : Nat)
    (hseen : run t = some (.D x y))
    (hstep : highLevelNext (.D x y) = some (.D aa dd))
    (hhalt : highLevelNext (.D aa dd) = none)
    (hyBound : y <= 177204)
    (hMassLo : 39367 <= x+y) :
    absDiff x (4*y) <= 128 ∨ absDiff y (4*x) <= 128 := by
  have hCorr :=
    blank_root_two_step_terminal_parent_corridor
      t x y aa dd hseen hstep hhalt
  rcases hCorr with ⟨hpos, hodd, heven, hnoGate⟩
  have hxEven : x % 2 = 0 := run_preserves_even t x y hseen
  have haaEven : aa % 2 = 0 :=
    next_preserves_even x y aa dd hxEven hstep
  have hMassCorr : x+y <= 17*y+68 := by
    by_cases hyOdd : y % 2 = 1
    · have h := hodd hyOdd
      omega
    · have hyEven : y % 2 = 0 := by omega
      have h := heven hyEven
      omega
  have hMass : x+y <= 3012536 := by omega
  have hKbase : 4*(x+y)+97 < 3^15 := by
    norm_num
    omega
  have hx0 : x ≠ 0 := by omega
  have hcR : 1 = 1 ∨ 1 = 2 := by omega
  have hcL : 5 = 5 ∨ 5 = 9 := by omega
  have hstepReduced := hstep

  by_cases hyOdd : y % 2 = 1
  · by_cases hfar : y+5 <= x
    · have hDrain : drainB (x-y-5) (y+3) 5 = some (.D aa dd) := by
        simp only [highLevelNext] at hstepReduced
        have h1 : y % 2 = 1 ∧ x >= y+5 := ⟨hyOdd, by omega⟩
        simp only [if_neg hx0, if_pos h1] at hstepReduced
        exact hstepReduced
      have hblock : y+3 < 3^12 := by norm_num at hyBound ⊢; omega
      have hK : 2*(x+2*y+10+3*12)+5 < 3^15 := by
        have hle : 2*(x+2*y+10+3*12)+5 <= 4*(x+y)+97 := by omega
        exact lt_of_le_of_lt hle hKbase
      rcases oddFar_terminal_ratio4_source
          x y 12 15 aa dd 1 5
          (by omega) hcR hcL hDrain hblock haaEven hhalt hK with
        ⟨hlo, hhi⟩
      left
      unfold absDiff
      by_cases hxy : x <= 4*y <;> omega
    · have hnear : x <= y+4 := by omega
      have hneq : x ≠ y+2 := by omega
      have hDrain : drainB (y+4-x) (x-1) 3 = some (.D aa dd) := by
        have hred := hstep
        simp only [highLevelNext] at hred
        have h1 : ¬ (y % 2 = 1 ∧ x >= y+5) := by simp [hyOdd, hfar]
        have h2 : ¬ (y % 2 = 0 ∧ x >= y+3) := by simp [hyOdd]
        have h3 : ¬ (x % 2 = 1) := by simp [hxEven]
        have h4 : x ≠ y+2 := hneq
        simp only [if_neg hx0, if_neg h1, if_neg h2, if_neg h3,
          if_neg h4, if_pos hyOdd] at hred
        exact hred
      have hblock : x-1 < 3^12 := by norm_num at hyBound ⊢; omega
      have hK : 2*(y+2*x+5+3*12)+5 < 3^15 := by
        have hle : 2*(y+2*x+5+3*12)+5 <= 4*(x+y)+97 := by omega
        exact lt_of_le_of_lt hle hKbase
      rcases oddNear_terminal_ratio4_source
          x y 12 15 aa dd 1 5
          hpos hnear hcR hcL hDrain hblock haaEven hhalt hK with
        ⟨hlo, hhi⟩
      right
      unfold absDiff
      by_cases hxy : y <= 4*x <;> omega
  · have hyEven : y % 2 = 0 := by omega
    by_cases hfar : y+3 <= x
    · have hDrain : drainB (x-y-2) (y+2) 2 = some (.D aa dd) := by
        have hred := hstep
        simp only [highLevelNext] at hred
        have h1 : ¬ (y % 2 = 1 ∧ x >= y+5) := by simp [hyEven]
        have h2 : y % 2 = 0 ∧ x >= y+3 := ⟨hyEven, by omega⟩
        simp only [if_neg hx0, if_neg h1, if_pos h2] at hred
        exact hred
      have hblock : y+2 < 3^12 := by norm_num at hyBound ⊢; omega
      have hK : 2*(x+2*y+7+3*12)+5 < 3^15 := by
        have hle : 2*(x+2*y+7+3*12)+5 <= 4*(x+y)+97 := by omega
        exact lt_of_le_of_lt hle hKbase
      rcases evenFar_terminal_ratio4_source
          x y 12 15 aa dd 1 5
          (by omega) hcR hcL hDrain hblock haaEven hhalt hK with
        ⟨hlo, hhi⟩
      left
      unfold absDiff
      by_cases hxy : x <= 4*y <;> omega
    · by_cases hgap : x = y+2
      · have hxlt : x < 3^16 := by
          have h := heven hyEven
          norm_num at hyBound ⊢
          omega
        have hroom : 2*16+6 <= 3*x := by omega
        have hgate : gateBudget x y 16 := by
          unfold gateBudget
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hyEven, hgap, hxlt, hroom⟩)))
        exact hnoGate 16 hgate
      · have hnear : x <= y := by omega
        have hEvalDrain :
            (evalA (y+1-x) x (2*x+5)).bind
              (fun z => match z with
                | (p,q,r) => drainB p q r) = some (.D aa dd) := by
          have hred := hstep
          simp only [highLevelNext] at hred
          have h1 : ¬ (y % 2 = 1 ∧ x >= y+5) := by simp [hyEven]
          have h2 : ¬ (y % 2 = 0 ∧ x >= y+3) := by simp [hyEven, hfar]
          have h3 : ¬ (x % 2 = 1) := by simp [hxEven]
          have h4 : x ≠ y+2 := hgap
          have h5 : ¬ (y % 2 = 1) := by omega
          simp only [if_neg hx0, if_neg h1, if_neg h2, if_neg h3,
            if_neg h4, if_neg h5] at hred
          exact hred
        simp only [Option.bind_eq_some_iff] at hEvalDrain
        rcases hEvalDrain with ⟨⟨p,q,r⟩, hEval, hDrain⟩
        have hxBound : x < 3^12 := by norm_num at hyBound ⊢; omega
        have hK : 2*(y+2*x+5+3*12)+5 < 3^15 := by
          have hle : 2*(y+2*x+5+3*12)+5 <= 4*(x+y)+97 := by omega
          exact lt_of_le_of_lt hle hKbase
        rcases evenNear_terminal_ratio4_source
            x y p q r 12 15 aa dd 1 5
            hpos hnear hxBound hcR hcL hEval hDrain haaEven hhalt hK with
          ⟨hlo, hhi⟩
        right
        unfold absDiff
        by_cases hxy : y <= 4*x <;> omega

#print axioms terminal_window_at_depth12

end BB6.Agent48TerminalWindowAtDepth12
