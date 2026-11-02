import RootShift
import CryptidsF287

namespace BB6.F287
open BB6Coverage

def eRoot : Fin 6 := ⟨4, by decide⟩
def dRoot : Fin 6 := ⟨3, by decide⟩

theorem e_prefix : run expectedRLE 1 (blankAt eRoot) =
    some (shiftConfig (-1) blank) := by
  change rawStep expectedRLE (blankAt eRoot) = some (shiftConfig (-1) blank)
  have hE : expectedRLE (eRoot, false) = some ⟨false,false,⟨0,by decide⟩⟩ := by decide
  simp only [rawStep, readSlot, blankAt, hE, Option.map_some]
  apply congrArg some
  simp [applyMove, shiftConfig, blank]

theorem d_step : rawStep expectedRLE (blankAt dRoot) =
    some (shiftConfig (-1) (blankAt eRoot)) := by
  have hD : expectedRLE (dRoot, false) = some ⟨false,false,eRoot⟩ := by decide
  simp only [rawStep, readSlot, blankAt, hD, Option.map_some]
  apply congrArg some
  simp [applyMove, shiftConfig, eRoot]

theorem d_prefix : run expectedRLE 2 (blankAt dRoot) =
    some (shiftConfig (-2) blank) := by
  change (rawStep expectedRLE (blankAt dRoot)).bind (rawStep expectedRLE) = _
  rw [d_step]
  simp only [Option.bind_some, shift_rawStep]
  change (rawStep expectedRLE (blankAt eRoot)).map (shiftConfig (-1)) = _
  have hE := e_prefix
  change rawStep expectedRLE (blankAt eRoot) = some (shiftConfig (-1) blank) at hE
  rw [hE]
  simp [shift_shift]

/-- The original machine's source-certified nonhalting A run transfers
to every start root with a finite prefix entering a translated blank A. -/
theorem root_after_prefix (s : Fin 6) (delay : Nat) (j : Int)
    (hp : run expectedRLE delay (blankAt s) = some (shiftConfig j blank))
    (n : Nat) :
    (run expectedRLE (delay+n) (blankAt s)).isSome = true := by
  rw [run_append, hp]
  exact live_shifted_blank expectedRLE j literal_never n

/-- Blank initial E deterministically enters shifted blank A in one move. -/
theorem e_never : ∀ n, (run expectedRLE n (blankAt eRoot)).isSome = true := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      rw [show n+1 = 1+n by omega]
      exact root_after_prefix eRoot 1 (-1) e_prefix n

/-- Blank initial D deterministically enters shifted blank A in two moves. -/
theorem d_never : ∀ n, (run expectedRLE n (blankAt dRoot)).isSome = true := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero =>
          change (rawStep expectedRLE (blankAt dRoot)).isSome = true
          rw [d_step]
          rfl
      | succ k =>
          rw [show k+1+1 = 2+k by omega]
          exact root_after_prefix dRoot 2 (-2) d_prefix k

#print axioms e_never
#print axioms d_never

end BB6.F287
