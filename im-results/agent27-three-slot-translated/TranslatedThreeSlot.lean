import TranslatedFiniteOracle
import FrontierMass

namespace BB6Coverage

/-- Three-slot blank-tape drift.  The head moves left to write a temporary
    marker, returns to erase it, and then advances into the next blank cell. -/
def agent27ThreeA0 : Slot := (⟨0, by decide⟩, false)
def agent27ThreeB0 : Slot := (⟨1, by decide⟩, false)
def agent27ThreeA1 : Slot := (⟨0, by decide⟩, true)

def agent27ThreeA0Action : Transition := some ⟨true, false, 1⟩
def agent27ThreeB0Action : Transition := some ⟨false, true, 0⟩
def agent27ThreeA1Action : Transition := some ⟨false, true, 0⟩

def agent27ThreeP0 : PartialMachine := emptyTable
def agent27ThreeP1 : PartialMachine :=
  refine agent27ThreeP0 agent27ThreeA0 agent27ThreeA0Action
def agent27ThreeP2 : PartialMachine :=
  refine agent27ThreeP1 agent27ThreeB0 agent27ThreeB0Action
def agent27ThreeP3 : PartialMachine :=
  refine agent27ThreeP2 agent27ThreeA1 agent27ThreeA1Action

/-- The three-step blank-root run returns to state A with a blank tape and
    head displacement +1.  The finite-support translation checker accepts. -/
theorem agent27Three_translated_check :
    finiteTranslatedCheck agent27ThreeP3 0 3 = true := by
  decide

/-- Every total completion of the three-slot table follows the translated
    blank configuration forever. -/
theorem agent27Three_cover (bound : Nat) :
    Cover (DecidedBelow bound) agent27ThreeP3 :=
  finiteTranslatedCheck_sound agent27ThreeP3 0 3 bound (by decide)
    agent27Three_translated_check

theorem agent27Three_never (m : Machine)
    (hm : compatible agent27ThreeP3 m) : NeverHalts m := by
  rcases (agent27Three_cover 0).sound m hm with hnever | ⟨n, hn, _⟩
  · exact hnever
  · omega

/-- Three assigned inputs leave exactly nine of the twelve rows free. -/
theorem agent27Three_mass : cylinderMass agent27ThreeP3 = 25^9 := by
  decide

theorem agent27Three_mass_numeric :
    cylinderMass agent27ThreeP3 = 3814697265625 := by
  calc
    cylinderMass agent27ThreeP3 = 25^9 := agent27Three_mass
    _ = 3814697265625 := by decide

#print axioms agent27Three_translated_check
#print axioms agent27Three_cover
#print axioms agent27Three_never
#print axioms agent27Three_mass
#print axioms agent27Three_mass_numeric

end BB6Coverage
