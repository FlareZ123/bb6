import Window5General
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Window5Witness
open BB6Coverage BB6.Agent50Window5

/-!
Literal Raw34 five-row refinement, leaving E0, F0, F1 genuinely free:
  1RB1RD_1RC0LE_0RD1RE_1LC1LA_---1LC_------
All 25 physical actions, HALT included, are allowed at each free slot.
The finite radius-two reachable-window certificate has 33 abstract
states; radius one alone reaches the still-free E0 slot. The source
Lean check below is decisive for the all-completions theorem.
-/

def parent : PartialMachine := fun s =>
  match s.1.val, s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true  => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true  => some (some ⟨false,false,4⟩)
  | 2,false => some (some ⟨false,true,3⟩)
  | 2,true  => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,2⟩)
  | 3,true  => some (some ⟨true,false,0⟩)
  | 4,true  => some (some ⟨true,false,2⟩)
  | _,_ => none

/-- Independent finite abstract BFS, bit order q*32 + L2*16 + L1*8
    + scanned*4 + R1*2 + R2. Each abstract move branches on both
    values of the newly exposed tape bit. -/
def windowMask : Nat := 0x3000300000ff00004f404c40f00003000c000c01

theorem start_checked :
    masked windowMask 0 false false false false false = true := by
  decide

theorem all_windows_checked :
    LocalOK parent (masked windowMask) := by
  apply localOK_of_check
  decide +kernel

/-- True original-blank all-time nonhalting, uniformly across the
    entire three-unassigned-slot 25^3 physical cylinder. -/
theorem never (m : Machine) (h : compatible parent m) :
    NeverHalts m :=
  never_of_localOK parent (masked windowMask)
    start_checked all_windows_checked m h

theorem cover (bound : Nat) : Cover (DecidedBelow bound) parent :=
  mask_cover windowMask parent bound start_checked all_windows_checked

#print axioms start_checked
#print axioms all_windows_checked
#print axioms never
#print axioms cover
end BB6.Agent50Window5Witness
