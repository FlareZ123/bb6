import TranslatedFiniteOracle
import FrontierMass

set_option maxRecDepth 16000
set_option maxHeartbeats 0

namespace BB6Coverage
namespace FiveStepBlankFamily

/-!
  Exact source-level candidate for 1200 five-step translated-blank cylinders.
  Each original-machine 5-step blank-to-blank displacement is in README.md.
  This module must compile under Lean4.36 with an axiom audit before being
  described as an accepted source theorem.
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

def p4 (b c d e : Fin 6) (right : Bool) : PartialMachine :=
  refine (p3 b c d right) (oneSlot d) (act false (!right) e)

/-- A0:1dB, B0:1(-d)C, C1:0dD, D1:0(-d)E, E0:0dA. -/
def table (b c d e : Fin 6) (right : Bool) : PartialMachine :=
  refine (p4 b c d e right) (zeroSlot e) (act false right 0)

/-- Exactly B != A, D != C, and E != A,B. -/
def tables : List PartialMachine :=
  directions.flatMap fun right =>
    nonStart.flatMap fun b =>
      allStates.flatMap fun c =>
        (allStates.filter (fun d => d != c)).flatMap fun d =>
          (allStates.filter (fun e => (e != 0) && (e != b))).map fun e =>
            table b c d e right

theorem table_count : tables.length = 1200 := by decide

theorem table_checks :
    tables.all (fun p => finiteTranslatedCheck p 0 5) = true := by
  decide

theorem table_cover (p : PartialMachine) (hp : p ∈ tables)
    (bound : Nat) : Cover (DecidedBelow bound) p :=
  finiteTranslatedCheck_sound p 0 5 bound (by decide)
    ((List.all_eq_true.mp table_checks) p hp)

theorem table_never (p : PartialMachine) (hp : p ∈ tables)
    (m : Machine) (hm : compatible p m) : NeverHalts m := by
  rcases (table_cover p hp 0).sound m hm with hnever | ⟨n, hn, _⟩
  · exact hnever
  · omega

theorem table_masses :
    tables.all (fun p => decide (cylinderMass p = 25^7)) = true := by
  decide

theorem table_mass (p : PartialMachine) (hp : p ∈ tables) :
    cylinderMass p = 25^7 :=
  (List.all_eq_true.mp table_masses) p hp

theorem union_mass_numeric :
    1200 * 25^7 = 7324218750000 := by decide

theorem union_fraction_numeric :
    1200 * 25^7 * 9765625 = 1200 * 25^12 := by decide

#print axioms table_count
#print axioms table_checks
#print axioms table_cover
#print axioms table_never
#print axioms table_masses
#print axioms table_mass
#print axioms union_mass_numeric
#print axioms union_fraction_numeric

end FiveStepBlankFamily
end BB6Coverage
