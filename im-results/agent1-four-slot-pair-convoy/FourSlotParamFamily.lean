import TranslatedFiniteOracle
import FrontierMass

set_option maxRecDepth 16000
set_option maxHeartbeats 0

namespace BB6Coverage
namespace FourSlotPairFamily

/-!
  Candidate source-proof for all 300 moving-pair cylinders.
  See README.md. The decidable certificates below require Lean4.36
  compilation and axiom audit before acceptance.
-/

def allStates : List (Fin 6) := List.finRange 6
def nonStart : List (Fin 6) := allStates.filter (fun s => s != 0)
def directions : List Bool := [false, true]

def a0 : Slot := ((0 : Fin 6), false)
def zeroSlot (s : Fin 6) : Slot := (s, false)
def oneSlot (s : Fin 6) : Slot := (s, true)

def act (write right : Bool) (next : Fin 6) : Transition :=
  some ⟨write, right, next⟩

def p1 (b : Fin 6) (right : Bool) : PartialMachine :=
  refine emptyTable a0 (act true right b)

def p2 (b c : Fin 6) (right : Bool) : PartialMachine :=
  refine (p1 b right) (zeroSlot b) (act true (!right) c)

def p3 (b c d : Fin 6) (right : Bool) : PartialMachine :=
  refine (p2 b c right) (oneSlot c) (act false right d)

/-- A0:1dB, B0:1(-d)C, C1:0dD, D1:1dB. -/
def table (b c d : Fin 6) (right : Bool) : PartialMachine :=
  refine (p3 b c d right) (oneSlot d) (act true right b)

/-- Exactly the legal four-row parameters: B != A and D != C. -/
def tables : List PartialMachine :=
  directions.flatMap fun right =>
    nonStart.flatMap fun b =>
      allStates.flatMap fun c =>
        (allStates.filter (fun d => d != c)).map fun d =>
          table b c d right

theorem table_count : tables.length = 300 := by decide

/-- Exact finite translated checker, all 300 member tables. -/
theorem table_checks :
    tables.all (fun p => finiteTranslatedCheck p 2 3) = true := by
  decide

theorem table_cover (p : PartialMachine) (hp : p ∈ tables)
    (bound : Nat) : Cover (DecidedBelow bound) p :=
  finiteTranslatedCheck_sound p 2 3 bound (by decide)
    ((List.all_eq_true.mp table_checks) p hp)

theorem table_never (p : PartialMachine) (hp : p ∈ tables)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  rcases (table_cover p hp 0).sound m hm with hnever | ⟨n, hn, _⟩
  · exact hnever
  · omega

/-- Each member fixes four distinct inputs and has 8 free inputs. -/
theorem table_masses :
    tables.all (fun p => decide (cylinderMass p = 25^8)) = true := by
  decide

theorem table_mass (p : PartialMachine) (hp : p ∈ tables) :
    cylinderMass p = 25^8 :=
  (List.all_eq_true.mp table_masses) p hp

theorem union_mass_numeric :
    300 * 25^8 = 45776367187500 := by decide

theorem union_fraction_numeric :
    300 * 25^8 * 390625 = 300 * 25^12 := by decide

#print axioms table_count
#print axioms table_checks
#print axioms table_cover
#print axioms table_never
#print axioms table_masses
#print axioms table_mass
#print axioms union_mass_numeric
#print axioms union_fraction_numeric

end FourSlotPairFamily
end BB6Coverage
