import TranslatedFiniteOracle
import FrontierMass

namespace BB6Coverage

/-- Four-slot blank-root translated cylinder.  The D/1 transition returns
    to B, reusing the already fixed B/0 transition at the final macro step. -/
def agent27FourA0 : Slot := (⟨0, by decide⟩, false)
def agent27FourB0 : Slot := (⟨1, by decide⟩, false)
def agent27FourC1 : Slot := (⟨2, by decide⟩, true)
def agent27FourD1 : Slot := (⟨3, by decide⟩, true)

def agent27FourA0Action : Transition := some ⟨true, true, 1⟩
def agent27FourB0Action : Transition := some ⟨true, false, 2⟩
def agent27FourC1Action : Transition := some ⟨false, true, 3⟩
def agent27FourD1Action : Transition := some ⟨true, true, 1⟩

def agent27FourP0 : PartialMachine := emptyTable
def agent27FourP1 : PartialMachine :=
  refine agent27FourP0 agent27FourA0 agent27FourA0Action
def agent27FourP2 : PartialMachine :=
  refine agent27FourP1 agent27FourB0 agent27FourB0Action
def agent27FourP3 : PartialMachine :=
  refine agent27FourP2 agent27FourC1 agent27FourC1Action
def agent27FourP4 : PartialMachine :=
  refine agent27FourP3 agent27FourD1 agent27FourD1Action

/-- After two blank-root moves the machine is at C/head 0 with marks {0,1};
    the three-step C/1,D/1,B/0 macro returns to C/head 1 with marks {1,2}. -/
theorem agent27Four_translated_check :
    finiteTranslatedCheck agent27FourP4 2 3 = true := by
  decide

/-- Every total completion of the four-slot cylinder follows the translated
    finite-support cycle forever. -/
theorem agent27Four_cover (bound : Nat) :
    Cover (DecidedBelow bound) agent27FourP4 :=
  finiteTranslatedCheck_sound agent27FourP4 2 3 bound (by decide)
    agent27Four_translated_check

theorem agent27Four_never (m : Machine)
    (hm : compatible agent27FourP4 m) : NeverHalts m := by
  rcases (agent27Four_cover 0).sound m hm with hnever | ⟨n, hn, _⟩
  · exact hnever
  · omega

/-- Four assigned inputs leave exactly eight of the twelve rows free. -/
theorem agent27Four_mass : cylinderMass agent27FourP4 = 25^8 := by
  decide

theorem agent27Four_mass_numeric :
    cylinderMass agent27FourP4 = 152587890625 := by
  calc
    cylinderMass agent27FourP4 = 25^8 := agent27Four_mass
    _ = 152587890625 := by decide

#print axioms agent27Four_translated_check
#print axioms agent27Four_cover
#print axioms agent27Four_never
#print axioms agent27Four_mass
#print axioms agent27Four_mass_numeric

end BB6Coverage
