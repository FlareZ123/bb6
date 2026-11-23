import Lean.Elab.Tactic.Omega
import ACodeFirstReturn
import AZeroOneFirstReturn

/-!
# Uniform exact first state-F return for mixed A-word + a single terminal one

For arbitrary finite mixed 10/111 token sequence ws, the physical original
six-state A-section with right tape wordCode(ws) ++ [1] ends at its first
F-state after the exact mixed-word clock and the A-one D sweep.
The final zero is genuinely implicit (infinite blank tape).
-/

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

namespace BB6.Agent4AImplicitOne

open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidACodeFirstReturn

def oneCost (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32)+
    (CryptidA.wordCost (4*k+3) ws+
      (2*(4*k+3+CryptidA.wordInc ws)+10))

def oneStart (k : Nat) (ws : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false::(CryptidA.wordCode ws ++ [true]))

def oneEnd (k : Nat) (ws : List Bool) : Cfg :=
  ⟨[],false,
    List.replicate (2*(4*k+3+CryptidA.wordInc ws)+7) true,5⟩

/-- Composing code consumption and a last-one close, original machine. -/
private theorem suffix_one_run (m : Nat) (ws : List Bool) :
    run (CryptidA.wordCost m ws+
        (2*(m+CryptidA.wordInc ws)+10))
      (aBoundary m (CryptidA.wordCode ws ++ [true])) =
    ⟨[],false,
      List.replicate (2*(m+CryptidA.wordInc ws)+7) true,5⟩ := by
  change run (CryptidA.wordCost m ws+
      (2*(m+CryptidA.wordInc ws)+10))
    (BB6.Agent35.aBoundary m
      (CryptidA.wordCode ws ++ [true])) = _
  rw [run_add,BB6.Agent35.a_code_return]
  change run (2*(m+CryptidA.wordInc ws)+10)
    (BB6.AOneSource.ab (m+CryptidA.wordInc ws) [true]) = _
  exact BB6.AOneSource.a_one_close (m+CryptidA.wordInc ws)

/-- No F occurs during any complete mixed code or its final A-one close.
This reuses the checked source token scanner, not a separate simulator. -/
private theorem suffix_one_noF (m : Nat) (ws : List Bool) :
    ∀ t, t<CryptidA.wordCost m ws+
        (2*(m+CryptidA.wordInc ws)+10) →
      (run t (aBoundary m (CryptidA.wordCode ws ++ [true]))).st ≠5 := by
  intro t ht
  by_cases hp : t<CryptidA.wordCost m ws
  · exact original_word_noF m ws [true] t hp
  · have hsplit : t=CryptidA.wordCost m ws+
        (t-CryptidA.wordCost m ws) := by omega
    rw [hsplit,run_add]
    change (run (t-CryptidA.wordCost m ws)
      (run (CryptidA.wordCost m ws)
        (BB6.Agent35.aBoundary m
          (CryptidA.wordCode ws ++ [true])))).st ≠5
    rw [BB6.Agent35.a_code_return]
    change (run (t-CryptidA.wordCost m ws)
      (BB6.AOneSource.ab (m+CryptidA.wordInc ws) [true])).st ≠5
    exact BB6.CryptidARegularFirstReturn.ab_one_close_noF
      (m+CryptidA.wordInc ws)
      (t-CryptidA.wordCost m ws) (by omega)

/-- The source F-section with any finite mixed A-code followed by a single
one has its first F visit at the exact positive endpoint. -/
theorem one_unpadded_strict_first (k : Nat) (ws : List Bool) :
    run (oneCost k ws) (oneStart k ws) = oneEnd k ws ∧
    ∀ t, 0<t → t<oneCost k ws →
      (run t (oneStart k ws)).st ≠5 := by
  constructor
  · have htime : oneCost k ws =
      (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws+
        (2*(4*k+3+CryptidA.wordInc ws)+10)) := rfl
    rw [htime,run_add]
    change run (CryptidA.wordCost (4*k+3) ws+
        (2*(4*k+3+CryptidA.wordInc ws)+10))
      (run (12*k*k+41*k+32)
        (init (List.replicate (3*k+1) true ++
          false::(CryptidA.wordCode ws ++ [true])))) = _
    rw [prefix_A]
    change run (CryptidA.wordCost (4*k+3) ws+
        (2*(4*k+3+CryptidA.wordInc ws)+10))
      (aBoundary (4*k+3) (CryptidA.wordCode ws ++ [true])) = _
    rw [suffix_one_run]
    rfl
  · intro t htpos ht
    by_cases hpref : t<12*k*k+41*k+32
    · change (run t (init (List.replicate (3*k+1) true ++
        false::(CryptidA.wordCode ws ++ [true])))).st ≠5
      exact prefixA_positive_noF k
        (CryptidA.wordCode ws ++ [true]) t htpos hpref
    · have htime : t=(12*k*k+41*k+32)+
          (t-(12*k*k+41*k+32)) := by omega
      rw [htime,run_add]
      change (run (t-(12*k*k+41*k+32))
        (run (12*k*k+41*k+32)
          (init (List.replicate (3*k+1) true ++
            false::(CryptidA.wordCode ws ++ [true]))))).st ≠5
      rw [prefix_A]
      change (run (t-(12*k*k+41*k+32))
        (aBoundary (4*k+3) (CryptidA.wordCode ws ++ [true]))).st ≠5
      exact suffix_one_noF (4*k+3) ws
        (t-(12*k*k+41*k+32))
        (by dsimp [oneCost] at ht; omega)

#print axioms suffix_one_run
#print axioms suffix_one_noF
#print axioms one_unpadded_strict_first

end BB6.Agent4AImplicitOne
