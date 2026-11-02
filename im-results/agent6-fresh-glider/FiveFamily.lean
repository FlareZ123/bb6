import MacroOracle

namespace BB6Coverage

/-- A five-move marker-bounce template. Four distinct noninitial states
    ensure the five consulted input slots are distinct. Both arbitrary
    write bits x,y leave the frontier cell blank upon macro completion. -/
def fiveTemplate (right : Bool) (b c d e : Fin 6) (x y : Bool) :
    PartialMachine := fun slot =>
  if slot = (0,false) then some (some ⟨true,right,b⟩)
  else if slot = (b,false) then some (some ⟨true,!right,c⟩)
  else if slot = (c,true) then some (some ⟨x,right,d⟩)
  else if slot = (d,true) then some (some ⟨false,!right,e⟩)
  else if slot = (e,x) then some (some ⟨y,right,0⟩)
  else none

def fiveDistinct (b c d e : Fin 6) : Bool :=
  b != 0 && c != 0 && d != 0 && e != 0 &&
    b != c && b != d && b != e && c != d && c != e && d != e

/-- Finite, explicit list: 5 choices of b, 4·3·2 for c,d,e, and
    two bits x,y, so 480 right and 480 left sparse cylinders. -/
def fiveFamilyFor (right : Bool) (b : Fin 6) : List PartialMachine :=
  (List.finRange 6).flatMap (fun c =>
    (List.finRange 6).flatMap (fun d =>
      (List.finRange 6).flatMap (fun e =>
        if fiveDistinct b c d e then
          ([false,true] : List Bool).flatMap (fun x =>
            ([false,true] : List Bool).map (fun y =>
              fiveTemplate right b c d e x y))
        else [])))

def fiveRightFamily : List PartialMachine :=
  (List.finRange 6).flatMap (fiveFamilyFor true)

def fiveLeftFamily : List PartialMachine :=
  (List.finRange 6).flatMap (fiveFamilyFor false)

theorem five_right_family_count : fiveRightFamily.length = 480 := by decide
theorem five_left_family_count : fiveLeftFamily.length = 480 := by decide

set_option maxRecDepth 16384
set_option maxHeartbeats 0

theorem five_right_family_check :
    fiveRightFamily.all (fun p => finiteMacroRightCheck p 5 1) = true := by decide

theorem five_left_family_check :
    fiveLeftFamily.all (fun p => finiteMacroLeftCheck p 5 1) = true := by decide

/-- Every member of the 480-element right list is a universally certified
    nonhalting sparse leaf for all its total completions. -/
theorem five_right_family_sound (p : PartialMachine) (bound : Nat)
    (hp : p ∈ fiveRightFamily) : Cover (DecidedBelow bound) p := by
  have hc : finiteMacroRightCheck p 5 1 = true :=
    (List.all_eq_true.mp five_right_family_check) p hp
  exact finiteMacroRightCheck_sound p 5 1 bound
    (by decide) (by decide) hc

theorem five_left_family_sound (p : PartialMachine) (bound : Nat)
    (hp : p ∈ fiveLeftFamily) : Cover (DecidedBelow bound) p := by
  have hc : finiteMacroLeftCheck p 5 1 = true :=
    (List.all_eq_true.mp five_left_family_check) p hp
  exact finiteMacroLeftCheck_sound p 5 1 bound
    (by decide) (by decide) hc

#print axioms five_right_family_sound
#print axioms five_left_family_sound

end BB6Coverage
