import Window7General
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window7Witness
open BB6Coverage BB6.Agent50Window7

/-!
Literal original two-symbol six-state Raw34 child, all physical
completions. No assumption on E0, F0, F1, including HALT at any
of these three slots:

  1RB0LB_1RC1LE_0RD1RC_1LC1LA_---0RA_------

The witness is a 75-state inductive seven-cell tape relation and is
checked against BOTH incoming tape-bit values at every step.
-/

def parent : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨false,false,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨true,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,false,0⟩)
  | 4,true  => some (some ⟨false,true,0⟩)
  | _,_ => none

def invariant : Nat := 0xf000000000000000f0000000000000000000ffff00000000000000000000000000ff00000000000000ff000000000000ff0f000000000000000f00000003000000f0ff000000000000f0000000000001

theorem start :
    masked7 invariant 0 false false false false false false false = true := by
  decide

theorem local :
    LocalOK7 parent (masked7 invariant) := by
  apply localOK7_of_check
  decide +kernel

theorem never (m : Machine) (hm : compatible parent m) :
    NeverHalts m :=
  never_of_localOK7 parent (masked7 invariant) start local m hm

theorem cover (bound : Nat) : Cover (DecidedBelow bound) parent := by
  apply Cover.leaf parent
  intro m hm
  exact Or.inl (never m hm)

#print axioms start
#print axioms local
#print axioms never
#print axioms cover
end BB6.Agent50Window7Witness
