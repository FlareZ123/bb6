import Overwrite55
import OverwriteOracle

namespace BB6Overwrite
open BB6Coverage

/-! The 55 exact literal hard-root tables are independently checked by a
finite Boolean sufficient oracle. Each Boolean check is axiom-free, while its
all-time consequence depends only on the source-sound raw-machine theorem.
All unrelated fatal paths remain unresolved. -/

theorem root9_checked :
    forbiddenCheck root9 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true = true := by decide

theorem root9_checked_sound (n : Nat) (c : Config)
    (hr : run root9 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root9 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root9 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true root9_checked n c hr hs

#print axioms root9_checked_sound

theorem root31_checked :
    forbiddenCheck root31 ⟨5, by decide⟩ true true true ⟨1, by decide⟩ true = true := by decide

theorem root31_checked_sound (n : Nat) (c : Config)
    (hr : run root31 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root31 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root31 ⟨5, by decide⟩ true true true ⟨1, by decide⟩ true root31_checked n c hr hs

#print axioms root31_checked_sound

theorem root45_checked :
    forbiddenCheck root45 ⟨5, by decide⟩ true false true ⟨3, by decide⟩ true = true := by decide

theorem root45_checked_sound (n : Nat) (c : Config)
    (hr : run root45 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root45 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root45 ⟨5, by decide⟩ true false true ⟨3, by decide⟩ true root45_checked n c hr hs

#print axioms root45_checked_sound

theorem root52_checked :
    forbiddenCheck root52 ⟨4, by decide⟩ false true true ⟨5, by decide⟩ true = true := by decide

theorem root52_checked_sound (n : Nat) (c : Config)
    (hr : run root52 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, false)) :
    ∃ d, rawStep root52 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root52 ⟨4, by decide⟩ false true true ⟨5, by decide⟩ true root52_checked n c hr hs

#print axioms root52_checked_sound

theorem root66_checked :
    forbiddenCheck root66 ⟨2, by decide⟩ false true false ⟨3, by decide⟩ true = true := by decide

theorem root66_checked_sound (n : Nat) (c : Config)
    (hr : run root66 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root66 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root66 ⟨2, by decide⟩ false true false ⟨3, by decide⟩ true root66_checked n c hr hs

#print axioms root66_checked_sound

theorem root71_checked :
    forbiddenCheck root71 ⟨5, by decide⟩ true true true ⟨1, by decide⟩ false = true := by decide

theorem root71_checked_sound (n : Nat) (c : Config)
    (hr : run root71 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root71 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root71 ⟨5, by decide⟩ true true true ⟨1, by decide⟩ false root71_checked n c hr hs

#print axioms root71_checked_sound

theorem root76_checked :
    forbiddenCheck root76 ⟨3, by decide⟩ false true true ⟨5, by decide⟩ true = true := by decide

theorem root76_checked_sound (n : Nat) (c : Config)
    (hr : run root76 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root76 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root76 ⟨3, by decide⟩ false true true ⟨5, by decide⟩ true root76_checked n c hr hs

#print axioms root76_checked_sound

theorem root105_checked :
    forbiddenCheck root105 ⟨2, by decide⟩ false true false ⟨3, by decide⟩ true = true := by decide

theorem root105_checked_sound (n : Nat) (c : Config)
    (hr : run root105 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root105 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root105 ⟨2, by decide⟩ false true false ⟨3, by decide⟩ true root105_checked n c hr hs

#print axioms root105_checked_sound

theorem root110_checked :
    forbiddenCheck root110 ⟨4, by decide⟩ true true true ⟨5, by decide⟩ true = true := by decide

theorem root110_checked_sound (n : Nat) (c : Config)
    (hr : run root110 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root110 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root110 ⟨4, by decide⟩ true true true ⟨5, by decide⟩ true root110_checked n c hr hs

#print axioms root110_checked_sound

theorem root132_checked :
    forbiddenCheck root132 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true = true := by decide

theorem root132_checked_sound (n : Nat) (c : Config)
    (hr : run root132 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root132 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root132 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true root132_checked n c hr hs

#print axioms root132_checked_sound

theorem root135_checked :
    forbiddenCheck root135 ⟨2, by decide⟩ true true true ⟨4, by decide⟩ false = true := by decide

theorem root135_checked_sound (n : Nat) (c : Config)
    (hr : run root135 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, true)) :
    ∃ d, rawStep root135 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root135 ⟨2, by decide⟩ true true true ⟨4, by decide⟩ false root135_checked n c hr hs

#print axioms root135_checked_sound

theorem root142_checked :
    forbiddenCheck root142 ⟨4, by decide⟩ true false true ⟨5, by decide⟩ false = true := by decide

theorem root142_checked_sound (n : Nat) (c : Config)
    (hr : run root142 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root142 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root142 ⟨4, by decide⟩ true false true ⟨5, by decide⟩ false root142_checked n c hr hs

#print axioms root142_checked_sound

theorem root144_checked :
    forbiddenCheck root144 ⟨3, by decide⟩ false false true ⟨4, by decide⟩ true = true := by decide

theorem root144_checked_sound (n : Nat) (c : Config)
    (hr : run root144 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root144 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root144 ⟨3, by decide⟩ false false true ⟨4, by decide⟩ true root144_checked n c hr hs

#print axioms root144_checked_sound

theorem root159_checked :
    forbiddenCheck root159 ⟨2, by decide⟩ true true true ⟨3, by decide⟩ false = true := by decide

theorem root159_checked_sound (n : Nat) (c : Config)
    (hr : run root159 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, true)) :
    ∃ d, rawStep root159 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root159 ⟨2, by decide⟩ true true true ⟨3, by decide⟩ false root159_checked n c hr hs

#print axioms root159_checked_sound

theorem root173_checked :
    forbiddenCheck root173 ⟨3, by decide⟩ true true true ⟨5, by decide⟩ false = true := by decide

theorem root173_checked_sound (n : Nat) (c : Config)
    (hr : run root173 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, true)) :
    ∃ d, rawStep root173 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root173 ⟨3, by decide⟩ true true true ⟨5, by decide⟩ false root173_checked n c hr hs

#print axioms root173_checked_sound

theorem root182_checked :
    forbiddenCheck root182 ⟨5, by decide⟩ false false true ⟨1, by decide⟩ true = true := by decide

theorem root182_checked_sound (n : Nat) (c : Config)
    (hr : run root182 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root182 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root182 ⟨5, by decide⟩ false false true ⟨1, by decide⟩ true root182_checked n c hr hs

#print axioms root182_checked_sound

theorem root191_checked :
    forbiddenCheck root191 ⟨1, by decide⟩ true false false ⟨5, by decide⟩ true = true := by decide

theorem root191_checked_sound (n : Nat) (c : Config)
    (hr : run root191 n blank = some c)
    (hs : readSlot c = (⟨1, by decide⟩, true)) :
    ∃ d, rawStep root191 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root191 ⟨1, by decide⟩ true false false ⟨5, by decide⟩ true root191_checked n c hr hs

#print axioms root191_checked_sound

theorem root204_checked :
    forbiddenCheck root204 ⟨3, by decide⟩ false true true ⟨4, by decide⟩ true = true := by decide

theorem root204_checked_sound (n : Nat) (c : Config)
    (hr : run root204 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root204 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root204 ⟨3, by decide⟩ false true true ⟨4, by decide⟩ true root204_checked n c hr hs

#print axioms root204_checked_sound

theorem root232_checked :
    forbiddenCheck root232 ⟨2, by decide⟩ false true false ⟨3, by decide⟩ false = true := by decide

theorem root232_checked_sound (n : Nat) (c : Config)
    (hr : run root232 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root232 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root232 ⟨2, by decide⟩ false true false ⟨3, by decide⟩ false root232_checked n c hr hs

#print axioms root232_checked_sound

theorem root233_checked :
    forbiddenCheck root233 ⟨5, by decide⟩ true true true ⟨4, by decide⟩ true = true := by decide

theorem root233_checked_sound (n : Nat) (c : Config)
    (hr : run root233 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root233 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root233 ⟨5, by decide⟩ true true true ⟨4, by decide⟩ true root233_checked n c hr hs

#print axioms root233_checked_sound

theorem root278_checked :
    forbiddenCheck root278 ⟨4, by decide⟩ false true true ⟨0, by decide⟩ true = true := by decide

theorem root278_checked_sound (n : Nat) (c : Config)
    (hr : run root278 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, false)) :
    ∃ d, rawStep root278 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root278 ⟨4, by decide⟩ false true true ⟨0, by decide⟩ true root278_checked n c hr hs

#print axioms root278_checked_sound

theorem root286_checked :
    forbiddenCheck root286 ⟨4, by decide⟩ true false false ⟨2, by decide⟩ false = true := by decide

theorem root286_checked_sound (n : Nat) (c : Config)
    (hr : run root286 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root286 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root286 ⟨4, by decide⟩ true false false ⟨2, by decide⟩ false root286_checked n c hr hs

#print axioms root286_checked_sound

theorem root289_checked :
    forbiddenCheck root289 ⟨4, by decide⟩ false true true ⟨5, by decide⟩ true = true := by decide

theorem root289_checked_sound (n : Nat) (c : Config)
    (hr : run root289 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, false)) :
    ∃ d, rawStep root289 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root289 ⟨4, by decide⟩ false true true ⟨5, by decide⟩ true root289_checked n c hr hs

#print axioms root289_checked_sound

theorem root296_checked :
    forbiddenCheck root296 ⟨4, by decide⟩ true true true ⟨0, by decide⟩ true = true := by decide

theorem root296_checked_sound (n : Nat) (c : Config)
    (hr : run root296 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root296 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root296 ⟨4, by decide⟩ true true true ⟨0, by decide⟩ true root296_checked n c hr hs

#print axioms root296_checked_sound

theorem root318_checked :
    forbiddenCheck root318 ⟨5, by decide⟩ false true false ⟨2, by decide⟩ true = true := by decide

theorem root318_checked_sound (n : Nat) (c : Config)
    (hr : run root318 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root318 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root318 ⟨5, by decide⟩ false true false ⟨2, by decide⟩ true root318_checked n c hr hs

#print axioms root318_checked_sound

theorem root325_checked :
    forbiddenCheck root325 ⟨3, by decide⟩ false false false ⟨4, by decide⟩ true = true := by decide

theorem root325_checked_sound (n : Nat) (c : Config)
    (hr : run root325 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root325 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root325 ⟨3, by decide⟩ false false false ⟨4, by decide⟩ true root325_checked n c hr hs

#print axioms root325_checked_sound

theorem root337_checked :
    forbiddenCheck root337 ⟨0, by decide⟩ true false true ⟨5, by decide⟩ false = true := by decide

theorem root337_checked_sound (n : Nat) (c : Config)
    (hr : run root337 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, true)) :
    ∃ d, rawStep root337 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root337 ⟨0, by decide⟩ true false true ⟨5, by decide⟩ false root337_checked n c hr hs

#print axioms root337_checked_sound

theorem root348_checked :
    forbiddenCheck root348 ⟨2, by decide⟩ false false true ⟨3, by decide⟩ false = true := by decide

theorem root348_checked_sound (n : Nat) (c : Config)
    (hr : run root348 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root348 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root348 ⟨2, by decide⟩ false false true ⟨3, by decide⟩ false root348_checked n c hr hs

#print axioms root348_checked_sound

theorem root355_checked :
    forbiddenCheck root355 ⟨5, by decide⟩ false true true ⟨3, by decide⟩ true = true := by decide

theorem root355_checked_sound (n : Nat) (c : Config)
    (hr : run root355 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root355 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root355 ⟨5, by decide⟩ false true true ⟨3, by decide⟩ true root355_checked n c hr hs

#print axioms root355_checked_sound

theorem root370_checked :
    forbiddenCheck root370 ⟨5, by decide⟩ true true true ⟨4, by decide⟩ true = true := by decide

theorem root370_checked_sound (n : Nat) (c : Config)
    (hr : run root370 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root370 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root370 ⟨5, by decide⟩ true true true ⟨4, by decide⟩ true root370_checked n c hr hs

#print axioms root370_checked_sound

theorem root388_checked :
    forbiddenCheck root388 ⟨3, by decide⟩ false true true ⟨4, by decide⟩ true = true := by decide

theorem root388_checked_sound (n : Nat) (c : Config)
    (hr : run root388 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root388 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root388 ⟨3, by decide⟩ false true true ⟨4, by decide⟩ true root388_checked n c hr hs

#print axioms root388_checked_sound

theorem root395_checked :
    forbiddenCheck root395 ⟨4, by decide⟩ true false false ⟨5, by decide⟩ false = true := by decide

theorem root395_checked_sound (n : Nat) (c : Config)
    (hr : run root395 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root395 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root395 ⟨4, by decide⟩ true false false ⟨5, by decide⟩ false root395_checked n c hr hs

#print axioms root395_checked_sound

theorem root398_checked :
    forbiddenCheck root398 ⟨5, by decide⟩ false false true ⟨3, by decide⟩ true = true := by decide

theorem root398_checked_sound (n : Nat) (c : Config)
    (hr : run root398 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root398 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root398 ⟨5, by decide⟩ false false true ⟨3, by decide⟩ true root398_checked n c hr hs

#print axioms root398_checked_sound

theorem root400_checked :
    forbiddenCheck root400 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true = true := by decide

theorem root400_checked_sound (n : Nat) (c : Config)
    (hr : run root400 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root400 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root400 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true root400_checked n c hr hs

#print axioms root400_checked_sound

theorem root408_checked :
    forbiddenCheck root408 ⟨4, by decide⟩ true true true ⟨5, by decide⟩ false = true := by decide

theorem root408_checked_sound (n : Nat) (c : Config)
    (hr : run root408 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root408 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root408 ⟨4, by decide⟩ true true true ⟨5, by decide⟩ false root408_checked n c hr hs

#print axioms root408_checked_sound

theorem root421_checked :
    forbiddenCheck root421 ⟨2, by decide⟩ false true true ⟨3, by decide⟩ true = true := by decide

theorem root421_checked_sound (n : Nat) (c : Config)
    (hr : run root421 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root421 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root421 ⟨2, by decide⟩ false true true ⟨3, by decide⟩ true root421_checked n c hr hs

#print axioms root421_checked_sound

theorem root456_checked :
    forbiddenCheck root456 ⟨4, by decide⟩ true true false ⟨5, by decide⟩ true = true := by decide

theorem root456_checked_sound (n : Nat) (c : Config)
    (hr : run root456 n blank = some c)
    (hs : readSlot c = (⟨4, by decide⟩, true)) :
    ∃ d, rawStep root456 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root456 ⟨4, by decide⟩ true true false ⟨5, by decide⟩ true root456_checked n c hr hs

#print axioms root456_checked_sound

theorem root463_checked :
    forbiddenCheck root463 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true = true := by decide

theorem root463_checked_sound (n : Nat) (c : Config)
    (hr : run root463 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root463 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root463 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true root463_checked n c hr hs

#print axioms root463_checked_sound

theorem root468_checked :
    forbiddenCheck root468 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true = true := by decide

theorem root468_checked_sound (n : Nat) (c : Config)
    (hr : run root468 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root468 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root468 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true root468_checked n c hr hs

#print axioms root468_checked_sound

theorem root483_checked :
    forbiddenCheck root483 ⟨5, by decide⟩ true false true ⟨3, by decide⟩ true = true := by decide

theorem root483_checked_sound (n : Nat) (c : Config)
    (hr : run root483 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root483 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root483 ⟨5, by decide⟩ true false true ⟨3, by decide⟩ true root483_checked n c hr hs

#print axioms root483_checked_sound

theorem root488_checked :
    forbiddenCheck root488 ⟨5, by decide⟩ false false true ⟨3, by decide⟩ false = true := by decide

theorem root488_checked_sound (n : Nat) (c : Config)
    (hr : run root488 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root488 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root488 ⟨5, by decide⟩ false false true ⟨3, by decide⟩ false root488_checked n c hr hs

#print axioms root488_checked_sound

theorem root499_checked :
    forbiddenCheck root499 ⟨3, by decide⟩ true false true ⟨4, by decide⟩ true = true := by decide

theorem root499_checked_sound (n : Nat) (c : Config)
    (hr : run root499 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, true)) :
    ∃ d, rawStep root499 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root499 ⟨3, by decide⟩ true false true ⟨4, by decide⟩ true root499_checked n c hr hs

#print axioms root499_checked_sound

theorem root502_checked :
    forbiddenCheck root502 ⟨2, by decide⟩ false true true ⟨0, by decide⟩ true = true := by decide

theorem root502_checked_sound (n : Nat) (c : Config)
    (hr : run root502 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root502 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root502 ⟨2, by decide⟩ false true true ⟨0, by decide⟩ true root502_checked n c hr hs

#print axioms root502_checked_sound

theorem root505_checked :
    forbiddenCheck root505 ⟨3, by decide⟩ false false true ⟨4, by decide⟩ true = true := by decide

theorem root505_checked_sound (n : Nat) (c : Config)
    (hr : run root505 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root505 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root505 ⟨3, by decide⟩ false false true ⟨4, by decide⟩ true root505_checked n c hr hs

#print axioms root505_checked_sound

theorem root509_checked :
    forbiddenCheck root509 ⟨0, by decide⟩ true false true ⟨5, by decide⟩ false = true := by decide

theorem root509_checked_sound (n : Nat) (c : Config)
    (hr : run root509 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, true)) :
    ∃ d, rawStep root509 c = some d ∧
      d.state = ⟨5, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root509 ⟨0, by decide⟩ true false true ⟨5, by decide⟩ false root509_checked n c hr hs

#print axioms root509_checked_sound

theorem root546_checked :
    forbiddenCheck root546 ⟨3, by decide⟩ false true true ⟨4, by decide⟩ false = true := by decide

theorem root546_checked_sound (n : Nat) (c : Config)
    (hr : run root546 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root546 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root546 ⟨3, by decide⟩ false true true ⟨4, by decide⟩ false root546_checked n c hr hs

#print axioms root546_checked_sound

theorem root555_checked :
    forbiddenCheck root555 ⟨5, by decide⟩ true true true ⟨0, by decide⟩ true = true := by decide

theorem root555_checked_sound (n : Nat) (c : Config)
    (hr : run root555 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root555 c = some d ∧
      d.state = ⟨0, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root555 ⟨5, by decide⟩ true true true ⟨0, by decide⟩ true root555_checked n c hr hs

#print axioms root555_checked_sound

theorem root561_checked :
    forbiddenCheck root561 ⟨5, by decide⟩ false false true ⟨1, by decide⟩ true = true := by decide

theorem root561_checked_sound (n : Nat) (c : Config)
    (hr : run root561 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, false)) :
    ∃ d, rawStep root561 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root561 ⟨5, by decide⟩ false false true ⟨1, by decide⟩ true root561_checked n c hr hs

#print axioms root561_checked_sound

theorem root575_checked :
    forbiddenCheck root575 ⟨5, by decide⟩ true false true ⟨2, by decide⟩ false = true := by decide

theorem root575_checked_sound (n : Nat) (c : Config)
    (hr : run root575 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root575 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root575 ⟨5, by decide⟩ true false true ⟨2, by decide⟩ false root575_checked n c hr hs

#print axioms root575_checked_sound

theorem root579_checked :
    forbiddenCheck root579 ⟨1, by decide⟩ false false false ⟨2, by decide⟩ true = true := by decide

theorem root579_checked_sound (n : Nat) (c : Config)
    (hr : run root579 n blank = some c)
    (hs : readSlot c = (⟨1, by decide⟩, false)) :
    ∃ d, rawStep root579 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root579 ⟨1, by decide⟩ false false false ⟨2, by decide⟩ true root579_checked n c hr hs

#print axioms root579_checked_sound

theorem root595_checked :
    forbiddenCheck root595 ⟨3, by decide⟩ false true false ⟨4, by decide⟩ false = true := by decide

theorem root595_checked_sound (n : Nat) (c : Config)
    (hr : run root595 n blank = some c)
    (hs : readSlot c = (⟨3, by decide⟩, false)) :
    ∃ d, rawStep root595 c = some d ∧
      d.state = ⟨4, by decide⟩ ∧ d.tape d.head ≠ false := by
  exact forbiddenCheck_sound root595 ⟨3, by decide⟩ false true false ⟨4, by decide⟩ false root595_checked n c hr hs

#print axioms root595_checked_sound

theorem root599_checked :
    forbiddenCheck root599 ⟨5, by decide⟩ true false true ⟨2, by decide⟩ true = true := by decide

theorem root599_checked_sound (n : Nat) (c : Config)
    (hr : run root599 n blank = some c)
    (hs : readSlot c = (⟨5, by decide⟩, true)) :
    ∃ d, rawStep root599 c = some d ∧
      d.state = ⟨2, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root599 ⟨5, by decide⟩ true false true ⟨2, by decide⟩ true root599_checked n c hr hs

#print axioms root599_checked_sound

theorem root613_checked :
    forbiddenCheck root613 ⟨2, by decide⟩ false false true ⟨3, by decide⟩ true = true := by decide

theorem root613_checked_sound (n : Nat) (c : Config)
    (hr : run root613 n blank = some c)
    (hs : readSlot c = (⟨2, by decide⟩, false)) :
    ∃ d, rawStep root613 c = some d ∧
      d.state = ⟨3, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root613 ⟨2, by decide⟩ false false true ⟨3, by decide⟩ true root613_checked n c hr hs

#print axioms root613_checked_sound

theorem root617_checked :
    forbiddenCheck root617 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true = true := by decide

theorem root617_checked_sound (n : Nat) (c : Config)
    (hr : run root617 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root617 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root617 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true root617_checked n c hr hs

#print axioms root617_checked_sound

theorem root645_checked :
    forbiddenCheck root645 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true = true := by decide

theorem root645_checked_sound (n : Nat) (c : Config)
    (hr : run root645 n blank = some c)
    (hs : readSlot c = (⟨0, by decide⟩, false)) :
    ∃ d, rawStep root645 c = some d ∧
      d.state = ⟨1, by decide⟩ ∧ d.tape d.head ≠ true := by
  exact forbiddenCheck_sound root645 ⟨0, by decide⟩ false true true ⟨1, by decide⟩ true root645_checked n c hr hs

#print axioms root645_checked_sound

end BB6Overwrite
