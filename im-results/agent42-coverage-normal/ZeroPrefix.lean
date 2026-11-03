import FirstStep
import RootShift

namespace BB6Coverage

/-- The six-state transposition A ↔ B; this changes the distinguished
    blank start to the former B state, and carries the original A slot too. -/
def swapAB : StatePerm := swapToOne (0 : Fin 6)

theorem swapAB_maps_B : swapAB.forward (1 : Fin 6) = 0 := by
  decide

/-- An initial non-writing A/0-to-B instruction makes the tape genuinely
    blank at the new root B, shifted one position to the right. -/
theorem zeroRB_first_config (m : Machine)
    (hfirst : m initialSlot = some ⟨false,true,(1 : Fin 6)⟩) :
    run m 1 blank = some (shiftConfig 1 (blankAt 1)) := by
  simp only [run, Option.bind_some, rawStep, blank_reads_initial, hfirst,
    Option.map_some]
  apply congrArg some
  simp [applyMove, shiftConfig, blank, blankAt]
  funext x
  by_cases hx : x = 0 <;> simp [hx]

/-- Every later run is just the former B-blank-root run, translated by one
    tape cell, with no run-time inflation or truncation. -/
theorem zeroRB_shifted_suffix (m : Machine)
    (hfirst : m initialSlot = some ⟨false,true,(1 : Fin 6)⟩)
    (k : Nat) :
    run m (k+1) blank =
      (run m k (blankAt 1)).map (shiftConfig 1) := by
  rw [show k+1=1+k by omega, run_append]
  rw [zeroRB_first_config m hfirst]
  simp only [Option.bind_some]
  exact shift_run 1 m (blankAt 1) k

/-- The original blank-root halting score is precisely one step greater
    than the blank-root-B score when A/0 is the unmarked move 0RB. -/
theorem zeroRB_trim_haltsAt (m : Machine)
    (hfirst : m initialSlot = some ⟨false,true,(1 : Fin 6)⟩)
    (k : Nat) :
    HaltsAfter m (k+1) ↔ HaltsAfterAt m 1 k := by
  unfold HaltsAfter HaltsAfterAt
  rw [zeroRB_shifted_suffix m hfirst k,
      zeroRB_shifted_suffix m hfirst (k+1)]
  cases h : run m k (blankAt 1) <;>
    cases h2 : run m (k+1) (blankAt 1) <;> simp

/-- A concrete six-state transition-table permutation, with no new states
    and no change to any defined slot, makes a 0RB-rooted run one step
    shorter from the ordinary blank A root. -/
theorem zeroRB_trim_permuted (m : Machine)
    (hfirst : m initialSlot = some ⟨false,true,(1 : Fin 6)⟩)
    (k : Nat) :
    HaltsAfter m (k+1) ↔
      HaltsAfter (renameTable swapAB m) k := by
  have hr := rename_haltsAt_iff swapAB m (1 : Fin 6) k
  rw [swapAB_maps_B] at hr
  change HaltsAfter (renameTable swapAB m) k ↔ HaltsAfterAt m 1 k at hr
  exact (zeroRB_trim_haltsAt m hfirst k).trans hr.symm

#print axioms zeroRB_first_config
#print axioms zeroRB_shifted_suffix
#print axioms zeroRB_trim_haltsAt
#print axioms zeroRB_trim_permuted
end BB6Coverage
