import Frontier

namespace BB429RootEntry

open BB6Coverage

/-- A concrete move in the original six-state #429 table. -/
def move (w r : Bool) (q : Nat) : Transition :=
  some ⟨w, r, ⟨q, by omega⟩⟩

/-- The complete original #429 table, including the genuine D/1 halt. -/
def source429 : Machine := fun s =>
  match s.1.val, s.2 with
  | 0, false => move true true 1
  | 0, true  => move false false 5
  | 1, false => move true true 2
  | 1, true  => move true true 0
  | 2, false => move false true 3
  | 2, true  => move false true 1
  | 3, false => move true false 4
  | 3, true  => none
  | 4, false => move false false 0
  | 4, true  => move true false 4
  | 5, false => move true true 3
  | 5, true  => move true false 0

/-- A primitive tape write, in the same convention as rawStep. -/
def writeAt (tape : Int → Bool) (p : Int) (b : Bool) : Int → Bool :=
  fun x => if x = p then b else tape x

/-- The complete ordered write trace of the 35-step blank-root prefix. -/
def rootWrites : List (Int × Bool) :=
  [ (0,true), (1,true), (2,false), (3,true), (2,false),
    (1,false), (0,true), (-1,true), (0,true), (1,true),
    (2,true), (3,false), (4,true), (5,false), (6,true),
    (5,false), (4,false), (3,true), (4,true), (3,true),
    (2,true), (1,true), (0,true), (-1,true), (-2,false),
    (-3,true), (-2,true), (-1,false), (0,true), (1,false),
    (0,true), (-1,true), (0,true), (1,true), (2,true) ]

/-- Finite-support tape obtained by applying the ordered raw writes to blank. -/
def rootTape : Int → Bool :=
  rootWrites.foldl (fun t wb => writeAt t wb.1 wb.2) (fun _ => false)

/-- The canonical J(0,0) endpoint, with head at absolute coordinate 3. -/
def j00Config : Config :=
  { state := ⟨0, by omega⟩
    head := 3
    tape := rootTape }

/-- Exact raw root entry: the genuine blank A-root reaches J(0,0)
    after 35 primitive transitions. -/
theorem blank_reaches_j00_after_35 :
    run source429 35 blank = some j00Config := by
  simp [j00Config, rootTape, rootWrites, writeAt, run, rawStep,
    applyMove, readSlot, source429, move]

#print axioms blank_reaches_j00_after_35

end BB429RootEntry
