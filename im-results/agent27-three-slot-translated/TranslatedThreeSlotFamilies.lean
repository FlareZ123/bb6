import TranslatedFiniteOracle
import FrontierMass

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace BB6Coverage
namespace ThreeSlotFamilies

/-- The five noninitial control states. -/
abbrev NonAState := {s : Fin 6 // s ≠ (0 : Fin 6)}

def nonAStates : List NonAState :=
  [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩,
   ⟨4, by decide⟩, ⟨5, by decide⟩]

def directions : List Bool := [false, true]
def allStates : List (Fin 6) := List.finRange 6

def a0 : Slot := ((0 : Fin 6), false)
def zeroSlot (s : Fin 6) : Slot := (s, false)
def oneSlot (s : Fin 6) : Slot := (s, true)

def act (write right : Bool) (next : Fin 6) : Transition :=
  some ⟨write, right, next⟩

/-- Schema I: A/0 writes a marker and enters x; x/0 erases the
    temporary cell while returning to the origin; y/1 erases the marker
    and advances one cell.  The cycle has length three and displacement
    opposite to the first move. -/
def period3Table (x : NonAState) (y : Fin 6) (right : Bool) :
    PartialMachine :=
  refine
    (refine
      (refine emptyTable a0 (act true right x.val))
      (zeroSlot x.val) (act false (!right) y))
    (oneSlot y) (act false (!right) 0)

/-- Schema II: a four-step cycle advances two cells. -/
def period4Table (x : NonAState) (right : Bool) : PartialMachine :=
  refine
    (refine
      (refine emptyTable a0 (act true right x.val))
      (zeroSlot x.val) (act false (!right) 0))
    (oneSlot 0) (act false (!right) x.val)

/-- Schema III: a one-step entry reaches x on a blank cell; a three-step
    cycle writes and erases a marker while advancing x by one cell. -/
def entryOneTable (x : NonAState) (right : Bool) : PartialMachine :=
  refine
    (refine
      (refine emptyTable a0 (act false right x.val))
      (zeroSlot x.val) (act true (!right) 0))
    (oneSlot x.val) (act false right x.val)

/-- All 60 Schema-I parameter choices pass the exact finite translated
    checker, not a separately implemented simulator. -/
theorem period3_checks :
    ∀ (x : NonAState) (y : Fin 6) (right : Bool),
      finiteTranslatedCheck (period3Table x y right) 0 3 = true := by
  decide

/-- All 10 Schema-II parameter choices pass the exact finite translated
    checker. -/
theorem period4_checks :
    ∀ (x : NonAState) (right : Bool),
      finiteTranslatedCheck (period4Table x right) 0 4 = true := by
  decide

/-- All 10 Schema-III parameter choices pass the exact finite translated
    checker. -/
theorem entryOne_checks :
    ∀ (x : NonAState) (right : Bool),
      finiteTranslatedCheck (entryOneTable x right) 1 3 = true := by
  decide

theorem period3_cover (x : NonAState) (y : Fin 6)
    (right : Bool) (bound : Nat) :
    Cover (DecidedBelow bound) (period3Table x y right) :=
  finiteTranslatedCheck_sound (period3Table x y right) 0 3 bound
    (by decide) (period3_checks x y right)

theorem period4_cover (x : NonAState) (right : Bool) (bound : Nat) :
    Cover (DecidedBelow bound) (period4Table x right) :=
  finiteTranslatedCheck_sound (period4Table x right) 0 4 bound
    (by decide) (period4_checks x right)

theorem entryOne_cover (x : NonAState) (right : Bool) (bound : Nat) :
    Cover (DecidedBelow bound) (entryOneTable x right) :=
  finiteTranslatedCheck_sound (entryOneTable x right) 1 3 bound
    (by decide) (entryOne_checks x right)

theorem period3_never (x : NonAState) (y : Fin 6) (right : Bool)
    (m : Machine) (hm : compatible (period3Table x y right) m) :
    NeverHalts m := by
  rcases (period3_cover x y right 0).sound m hm with hnever | ⟨n, hn, hh⟩
  · exact hnever
  · omega

theorem period4_never (x : NonAState) (right : Bool)
    (m : Machine) (hm : compatible (period4Table x right) m) :
    NeverHalts m := by
  rcases (period4_cover x right 0).sound m hm with hnever | ⟨n, hn, hh⟩
  · exact hnever
  · omega

theorem entryOne_never (x : NonAState) (right : Bool)
    (m : Machine) (hm : compatible (entryOneTable x right) m) :
    NeverHalts m := by
  rcases (entryOne_cover x right 0).sound m hm with hnever | ⟨n, hn, hh⟩
  · exact hnever
  · omega

/-- Every member of each of the three parameterized families fixes exactly
    three distinct transition inputs, hence has 25^9 completions. -/
theorem period3_masses :
    ∀ (x : NonAState) (y : Fin 6) (right : Bool),
      cylinderMass (period3Table x y right) = 25^9 := by
  decide

theorem period4_masses :
    ∀ (x : NonAState) (right : Bool),
      cylinderMass (period4Table x right) = 25^9 := by
  decide

theorem entryOne_masses :
    ∀ (x : NonAState) (right : Bool),
      cylinderMass (entryOneTable x right) = 25^9 := by
  decide

/-- Exact finite family represented by the three schemas: 60 + 10 + 10. -/
def period3Tables : List PartialMachine :=
  nonAStates.flatMap fun x =>
    directions.flatMap fun right =>
      allStates.map fun y => period3Table x y right

def period4Tables : List PartialMachine :=
  nonAStates.flatMap fun x =>
    directions.map fun right => period4Table x right

def entryOneTables : List PartialMachine :=
  nonAStates.flatMap fun x =>
    directions.map fun right => entryOneTable x right

def candidateTables : List PartialMachine :=
  period3Tables ++ period4Tables ++ entryOneTables

theorem period3Tables_length : period3Tables.length = 60 := by decide
theorem period4Tables_length : period4Tables.length = 10 := by decide
theorem entryOneTables_length : entryOneTables.length = 10 := by decide
theorem candidateTables_length : candidateTables.length = 80 := by decide

/-- Two partial tables conflict when they assign different actions to a
    common transition input. -/
def partialConflict (p q : PartialMachine) : Prop :=
  ∃ s : Slot, p s ≠ none ∧ q s ≠ none ∧ p s ≠ q s

/-- A conflict makes the two completion cylinders disjoint. -/
theorem partialConflict_disjoint (p q : PartialMachine)
    (h : partialConflict p q) :
    ∀ m, ¬ (compatible p m ∧ compatible q m) := by
  rcases h with ⟨s, hp, hq, hne⟩
  cases hps : p s with
  | none => exact (hp hps).elim
  | some t =>
    cases hqs : q s with
    | none => exact (hq hqs).elim
    | some u =>
      intro m hm
      have ht : m s = t := hm.1 s t hps
      have hu : m s = u := hm.2 s u hqs
      apply hne
      simp [hps, hqs, ht.symm.trans hu]

/-- The 80 schemas are pairwise incompatible as partial transition tables.
    Thus their 80 cylinders are mutually disjoint, not merely distinct. -/
theorem candidateTables_pairwise_conflict :
    candidateTables.Pairwise partialConflict := by
  decide

/-- The disjoint union's exact mass, obtained from 80 cylinders of mass
    25^9.  The final identity expresses 0.512% of the 25^12 raw tables. -/
theorem candidateUnionMass :
    80 * 25^9 = 305175781250000 := by
  decide

theorem candidateUnionFraction :
    80 * 25^9 * 3125 = 16 * 25^12 := by
  decide

#print axioms period3_checks
#print axioms period4_checks
#print axioms entryOne_checks
#print axioms period3_cover
#print axioms period4_cover
#print axioms entryOne_cover
#print axioms period3_never
#print axioms period4_never
#print axioms entryOne_never
#print axioms period3_masses
#print axioms period4_masses
#print axioms entryOne_masses
#print axioms candidateTables_length
#print axioms candidateTables_pairwise_conflict
#print axioms partialConflict_disjoint
#print axioms candidateUnionMass
#print axioms candidateUnionFraction

end ThreeSlotFamilies
end BB6Coverage
