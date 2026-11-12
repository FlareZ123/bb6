import JPhysicalPrefix
import Lean.Elab.Tactic.Omega

namespace BB429RootEntry

open BB6Coverage BB429PhysicalFrontier BB429JPhysical

/-- A primitive tape write, in the same convention as rawStep. -/
def writeAt (tape : Int → Bool) (p : Int) (b : Bool) : Int → Bool :=
  fun x => if x = p then b else tape x

/-- The complete ordered write trace of the 35-step blank-root prefix.
    Repeated writes are retained so this is a literal fold of rawStep's
    tape-update operation. -/
def rootWrites : List (Int × Bool) :=
  [ (0,true), (1,true), (2,false), (3,true), (2,false),
    (1,false), (0,true), (-1,true), (0,true), (1,true),
    (2,true), (3,false), (4,true), (5,false), (6,true),
    (5,false), (4,false), (3,true), (4,true), (3,true),
    (2,true), (1,true), (0,true), (-1,true), (-2,false),
    (-3,true), (-2,true), (-1,false), (0,true), (1,false),
    (0,true), (-1,true), (0,true), (1,true), (2,true) ]

/-- Finite-support tape obtained by applying the above raw writes to blank. -/
def rootTape : Int → Bool :=
  rootWrites.foldl (fun t wb => writeAt t wb.1 wb.2) (fun _ => false)

/-- The canonical J(0,0) endpoint, in absolute coordinates. -/
def j00Config : Config :=
  { state := ⟨0, by decide⟩
    head := 3
    tape := rootTape }

/-- Exact root entry: the original #429 table takes the genuine blank
    A-root to the canonical J(0,0) physical tape in 35 primitive steps. -/
theorem blank_reaches_j00_after_35 :
    run target429 35 blank = some j00Config := by
  simp [j00Config, rootTape, rootWrites, writeAt, run, rawStep, applyMove,
    readSlot, target429, prefix11, prefix10, prefix9, prefix8, prefix7,
    prefix6, prefix5, prefix4, prefix3, prefix2, prefix1, prefix0]

#print axioms blank_reaches_j00_after_35

end BB429RootEntry
