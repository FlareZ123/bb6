import BubblePrefix
import BB429PhysicalFrontier
import Lean.Elab.Tactic.Omega

namespace BB429JPhysical
open BB6Coverage BB6Bubble BB429PhysicalFrontier

/-- Canonical symbolic J(u,w) tape in absolute coordinates with head at zero. -/
def jHole (u : Nat) (x : Int) : Prop :=
  -2*(u:Int) ≤ x ∧ x < 0 ∧ x%2=0

def jMark (u w : Nat) (x : Int) : Prop :=
  (-2*(u:Int)-6 ≤ x ∧ x ≤ (w:Int)+1 ∧ ¬jHole u x) ∨ x=(w:Int)+3

instance jMarkDecidable (u w : Nat) (x : Int) : Decidable (jMark u w x) := by
  unfold jMark jHole
  infer_instance

def jTape (u w : Nat) : Int → Bool := fun x => if jMark u w x then true else false

private theorem A1 : target429 (BB6Bubble.A,true) = some ⟨false,false,BB6Bubble.F⟩ := by decide
private theorem F1 : target429 (BB6Bubble.F,true) = some ⟨true,false,BB6Bubble.A⟩ := by decide
private theorem A0 : target429 (BB6Bubble.A,false) = some ⟨true,true,BB6Bubble.B⟩ := by decide
private theorem B1 : target429 (BB6Bubble.B,true) = some ⟨true,true,BB6Bubble.A⟩ := by decide

private theorem j_holes (u w : Nat) (i : Nat) (hi : i<u) :
    jTape u w (-2*((i+1:Nat):Int))=false := by
  have hh : ¬jMark u w (-2*((i:Int)+1)) := by
    unfold jMark jHole
    omega
  change (if jMark u w (-2*((i:Int)+1)) then true else false) = false
  exact ite_eq_right hh

private theorem j_odds (u w : Nat) (x : Int)
    (hlo : -2*(u:Int) < x) (hi : x<0) (hodd : x%2 ≠ 0) :
    jTape u w x=true := by
  have hh : jMark u w x := by
    unfold jMark jHole
    left
    constructor
    · omega
    constructor
    · omega
    · omega
  simp [jTape,hh]

private theorem j_right (u w : Nat) (hw : 2*u ≤ w+1) (x : Int)
    (hlo : 0≤x) (hi : x≤2*(u:Int)) : jTape u w x=true := by
  have hh : jMark u w x := by
    unfold jMark jHole
    left
    constructor
    · omega
    constructor
    · omega
    · omega
  simp [jTape,hh]

/-- Genuine primitive-step prefix for every symbolic J(u,w) whose right
    run of ones reaches at least coordinate 2u; this is an exact all-u
    kernel theorem, using the original #429 transition table. -/
theorem j_prefix_exact (u w : Nat) (hw : 2*u ≤ w+1) :
    run target429 (4*u*u+2*u) {state:=BB6Bubble.A,head:=0,tape:=jTape u w} =
    some {state:=BB6Bubble.A,head:=2*(u:Int),tape:=negFill (jTape u w) u} := by
  exact multi_bubble_prefix target429 u u (jTape u w) (by omega)
     A1 F1 A0 B1 (j_holes u w) (j_odds u w) (j_right u w hw)

#print axioms j_prefix_exact
end BB429JPhysical
