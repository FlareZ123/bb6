import Window5General
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window5Product
open BB6Coverage BB6.Agent50Window5

/-!
A radius-two all-time Raw34 invariant with a twelve-way, four-hole
product family. Every one of the 12 parents below has four genuinely
unassigned slots A1, E0, F0 and F1, which may each be HALT.

  A0=1RB B0=1RC C0=0RD D0=1LC C1=1RE,
  B1∈{0LE,0RD}, D1∈{1LA,1LC}, E1∈{0RD,1LC,1RC}.

The finite all-windows checker is internal to the Lean kernel. No
bounded tape, inferred blank tail, or finite-run extrapolation occurs.
-/

def bMove : Bool → Move
  | false => ⟨false,false,4⟩  -- 0LE
  | true  => ⟨false,true,3⟩   -- 0RD

def dMove : Bool → Move
  | false => ⟨true,false,0⟩  -- 1LA
  | true  => ⟨true,false,2⟩  -- 1LC

def eMove (e : Fin 3) : Move :=
  match e.val with
  | 0 => ⟨false,true,3⟩   -- 0RD
  | 1 => ⟨true,false,2⟩  -- 1LC
  | _ => ⟨true,true,2⟩   -- 1RC

def parent (b d : Bool) (e : Fin 3) : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some (bMove b))
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some (dMove d))
  | 4,true  => some (some (eMove e))
  | _,_ => none

/-- The 33 abstract states are indexed by
q*32 + 16*L2 + 8*L1 + 4*scanned + 2*R1 + R2. -/
def invariantMask : Nat :=
  0x3000300000ff00004f404c40f00003000c000c01

theorem start_checked :
    masked invariantMask 0 false false false false false = true := by
  decide

/-- Exactly 12 finite checker obligations; unlike a single literal
table, this closes a whole four-slot-freedom product uniformly. -/
theorem every_parent_checked :
    ∀ (b d : Bool) (e : Fin 3),
      LocalOK (parent b d e) (masked invariantMask) := by
  decide

theorem never (b d : Bool) (e : Fin 3)
    (m : Machine) (hm : compatible (parent b d e) m) :
    NeverHalts m :=
  never_of_localOK (parent b d e) (masked invariantMask)
    start_checked (every_parent_checked b d e) m hm

theorem cover (bound : Nat) (b d : Bool) (e : Fin 3) :
    Cover (DecidedBelow bound) (parent b d e) :=
  mask_cover invariantMask (parent b d e) bound
    start_checked (every_parent_checked b d e)

#print axioms start_checked
#print axioms every_parent_checked
#print axioms never
#print axioms cover
end BB6.Agent50Window5Product
