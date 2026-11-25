import BlockMacro

namespace BB6Carry
open BB6BlockFAR

/-- The two raw110 kid5 leaves differ only at F1. The hole is A1. -/
def machine (slow : Bool) : Table := fun q b =>
  match q.val,b with
  | 0,false => some ⟨true,true,1⟩
  | 0,true => none
  | 1,false => some ⟨true,true,2⟩
  | 1,true => some ⟨false,true,0⟩
  | 2,false => some ⟨false,true,3⟩
  | 2,true => some ⟨false,false,5⟩
  | 3,false => some ⟨true,false,3⟩
  | 3,true => some ⟨true,true,4⟩
  | 4,false => some ⟨false,true,1⟩
  | 4,true => some ⟨false,false,2⟩
  | 5,false => some ⟨true,false,2⟩
  | _,true => if slow then some ⟨true,true,3⟩ else some ⟨false,false,5⟩
  | _,false => none

inductive Phase where | B | F | C
  deriving DecidableEq, Repr

/-- Left pair 0 means nearest-first 01; pair 1 means nearest-first 10. -/
def leftPairs : List Bool → Ray
  | [] => blankRay
  | a::l => cons a (cons (!a) (leftPairs l))

def render (p : Phase) (l : List Bool) (r : Ray) : Prim :=
  match p with
  | .B => ⟨1,leftPairs l,r⟩
  | .F => ⟨5,tail (leftPairs l),cons (leftPairs l 0) r⟩
  | .C => ⟨2,tail (leftPairs l),cons (leftPairs l 0) r⟩

def bits : List Bool → Ray → Ray
  | [],r => r
  | a::w,r => cons a (bits w r)

theorem start (slow : Bool) : run (machine slow) 1 primBlank = some (render .B [true] blankRay) := by
  simp [run,primStep,machine,primBlank,render,leftPairs,blank_cons,tail,blankRay]
  rfl

theorem B10 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) 2 (render .B l (bits [true,false] r)) = some (render .B (true::l) r) := by
  cases slow <;> rfl

theorem B01 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) (if slow then 7 else 3) (render .B l (bits [false,true] r)) = some (render .F l (bits [false,false] r)) := by
  cases slow <;> rfl

theorem B000 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) 7 (render .B l (bits [false,false,false] r)) = some (render .F l (bits [false,false,true] r)) := by
  cases slow <;> rfl

theorem B0010 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) 4 (render .B l (bits [false,false,true,false] r)) = some (render .B (false::false::l) r) := by
  cases slow <;> rfl

theorem B0011 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) 7 (render .B l (bits [false,false,true,true] r)) = some (render .F l (bits [false,true,false,false] r)) := by
  cases slow <;> rfl

theorem F01 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) 2 (render .F (false::l) r) = some (render .F l (bits [false,true] r)) := by
  cases slow <;> rfl

/-- F1 requires a zero just to its right in the slow variant. The five-step
    replacement rejoins the fast transition's exact configuration. -/
theorem F10 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) (if slow then 6 else 2) (render .F (true::l) (cons false r)) = some (render .C l (bits [true,false,false] r)) := by
  cases slow <;> rfl

theorem C10 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) 2 (render .C (true::l) r) = some (render .C l (bits [true,false] r)) := by
  cases slow <;> rfl

theorem C01 (slow : Bool) (l : List Bool) (r : Ray) :
    run (machine slow) 3 (render .C (false::l) (bits [true,false] r)) = some (render .B (false::false::l) r) := by
  cases slow <;> rfl

theorem Cnil (slow : Bool) (r : Ray) :
    run (machine slow) 3 (render .C [] (bits [true,false] r)) = some (render .B [false] r) := by
  cases slow <;> change some (⟨1,cons false (cons true (cons false (tail blankRay))),r⟩ : Prim) = some (render .B [false] r)
  all_goals simp [render,leftPairs,show tail blankRay = blankRay by rfl,blank_cons]

theorem Fnil (slow : Bool) (r : Ray) :
    run (machine slow) 4 (render .F [] (cons false r)) = some (render .B [false] r) := by
  cases slow <;> change some (⟨1,cons false (cons true (cons false (tail (tail blankRay)))),r⟩ : Prim) = some (render .B [false] r)
  all_goals simp [render,leftPairs,show tail (tail blankRay) = blankRay by rfl,blank_cons]

#print axioms start
#print axioms B01
#print axioms F10
#print axioms Fnil
end BB6Carry
