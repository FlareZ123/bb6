import F412ThreeHoleGeneric
import NGramCertificate
import F412Depth6A10RFF01
import F412Depth6A10RFF02
import F412Depth6A10RFF03
import F412Depth6A10RFF04
import F412Depth6A10RFF07
import F412Depth6A10RFF12
import F412Depth6A10RFF15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth6.A10RF
open BB6Coverage BB6.Agent26F412Graft BB6.Agent26F412ThreeHole BB6.Agent26F412TwoHole BB6.Agent1NGram

def am : Move := ⟨false,true,5⟩
def branch (fm : Move) : PartialMachine := pA1F0 am fm

/-! F0 move 0: NGram width 3, 57 states. -/
def c0 : Cert := ⟨2,0x515,0x15ff,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) .empty)),.empty,(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))),(.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty))]⟩
theorem checked0 : check (branch ⟨false,false,0⟩) c0 = true := by decide
theorem child0 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,0⟩) c0 checked0 m hm)

/-! First F0 move 1 reaches another hole, fully covered by A10RFF01. -/
theorem child1 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,1⟩) m) : WeightedBound B m :=
  A10RFF01.parent_sound B hB m
    (by simpa [branch, A10RFF01.am, A10RFF01.fm,am,pA1F0] using hm)

/-! First F0 move 2 reaches another hole, fully covered by A10RFF02. -/
theorem child2 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,2⟩) m) : WeightedBound B m :=
  A10RFF02.parent_sound B hB m
    (by simpa [branch, A10RFF02.am, A10RFF02.fm,am,pA1F0] using hm)

/-! First F0 move 3 reaches another hole, fully covered by A10RFF03. -/
theorem child3 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,3⟩) m) : WeightedBound B m :=
  A10RFF03.parent_sound B hB m
    (by simpa [branch, A10RFF03.am, A10RFF03.fm,am,pA1F0] using hm)

/-! First F0 move 4 reaches another hole, fully covered by A10RFF04. -/
theorem child4 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,4⟩) m) : WeightedBound B m :=
  A10RFF04.parent_sound B hB m
    (by simpa [branch, A10RFF04.am, A10RFF04.fm,am,pA1F0] using hm)

/-! F0 move 5: NGram width 3, 15 states. -/
def c5 : Cert := ⟨2,0x115,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),.empty,(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),(.branch (.branch .empty .leaf) .empty),.leaf,(.branch .empty .leaf),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) .empty) .empty) .empty),(.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))]⟩
theorem checked5 : check (branch ⟨false,false,5⟩) c5 = true := by decide
theorem child5 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,5⟩) c5 checked5 m hm)

/-! F0 move 6: NGram width 3, 32 states. -/
def c6 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked6 : check (branch ⟨false,true,0⟩) c6 = true := by decide
theorem child6 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,0⟩) c6 checked6 m hm)

/-! First F0 move 7 reaches another hole, fully covered by A10RFF07. -/
theorem child7 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,1⟩) m) : WeightedBound B m :=
  A10RFF07.parent_sound B hB m
    (by simpa [branch, A10RFF07.am, A10RFF07.fm,am,pA1F0] using hm)

/-! F0 move 8: NGram width 3, 36 states. -/
def c8 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked8 : check (branch ⟨false,true,2⟩) c8 = true := by decide
theorem child8 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,2⟩) c8 checked8 m hm)

/-! F0 move 9: NGram width 3, 38 states. -/
def c9 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked9 : check (branch ⟨false,true,3⟩) c9 = true := by decide
theorem child9 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,3⟩) c9 checked9 m hm)

/-! F0 move 10: NGram width 3, 37 states. -/
def c10 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked10 : check (branch ⟨false,true,4⟩) c10 = true := by decide
theorem child10 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,4⟩) c10 checked10 m hm)

/-! F0 move 11: NGram width 3, 33 states. -/
def c11 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked11 : check (branch ⟨false,true,5⟩) c11 = true := by decide
theorem child11 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,5⟩) c11 checked11 m hm)

/-! First F0 move 12 reaches another hole, fully covered by A10RFF12. -/
theorem child12 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,0⟩) m) : WeightedBound B m :=
  A10RFF12.parent_sound B hB m
    (by simpa [branch, A10RFF12.am, A10RFF12.fm,am,pA1F0] using hm)

/-! F0 move 13: NGram width 3, 20 states. -/
def c13 : Cert := ⟨2,0xf355,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),(.branch (.branch .empty .leaf) .empty),.leaf,(.branch .empty .leaf),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked13 : check (branch ⟨true,false,1⟩) c13 = true := by decide
theorem child13 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,1⟩) c13 checked13 m hm)

/-! F0 move 14: NGram width 4, 71 states. -/
def c14 : Cert := ⟨3,0x100f15,0x503c55,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),.empty,(.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))]⟩
theorem checked14 : check (branch ⟨true,false,2⟩) c14 = true := by decide
theorem child14 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,2⟩) c14 checked14 m hm)

/-! First F0 move 15 reaches another hole, fully covered by A10RFF15. -/
theorem child15 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,3⟩) m) : WeightedBound B m :=
  A10RFF15.parent_sound B hB m
    (by simpa [branch, A10RFF15.am, A10RFF15.fm,am,pA1F0] using hm)

/-! F0 move 16: NGram width 3, 44 states. -/
def c16 : Cert := ⟨2,0x515,0x15ff,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)),.empty,(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .leaf)),(.branch (.branch .empty (.branch .leaf .leaf)) .empty),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty))]⟩
theorem checked16 : check (branch ⟨true,false,4⟩) c16 = true := by decide
theorem child16 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,4⟩) c16 checked16 m hm)

/-! F0 move 17: NGram width 3, 26 states. -/
def c17 : Cert := ⟨2,0x115,0xc055,#[.leaf,(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),.empty,(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),(.branch (.branch .empty .leaf) .empty),.leaf,(.branch .empty .leaf),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch .leaf .leaf) .leaf))),(.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))]⟩
theorem checked17 : check (branch ⟨true,false,5⟩) c17 = true := by decide
theorem child17 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,5⟩) c17 checked17 m hm)

/-! F0 move 18: NGram width 4, 88 states. -/
def c18 : Cert := ⟨3,0xf35c5df5,0x502c55,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) .empty) .empty) .empty) (.branch (.branch .leaf (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) .empty)) .empty)),.empty,(.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))) .empty))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),(.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) .empty))) .empty),(.branch (.branch .leaf (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)) .empty),(.branch .empty (.branch .leaf (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)) .empty)),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) .empty)) .empty))]⟩
theorem checked18 : check (branch ⟨true,true,0⟩) c18 = true := by decide
theorem child18 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,0⟩) c18 checked18 m hm)

/-! F0 move 19: NGram width 3, 25 states. -/
def c19 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked19 : check (branch ⟨true,true,1⟩) c19 = true := by decide
theorem child19 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,1⟩) c19 checked19 m hm)

/-! F0 move 20: NGram width 3, 29 states. -/
def c20 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked20 : check (branch ⟨true,true,2⟩) c20 = true := by decide
theorem child20 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,2⟩) c20 checked20 m hm)

/-! F0 move 21: NGram width 3, 31 states. -/
def c21 : Cert := ⟨2,0xffdd,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked21 : check (branch ⟨true,true,3⟩) c21 = true := by decide
theorem child21 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,3⟩) c21 checked21 m hm)

/-! F0 move 22: NGram width 3, 30 states. -/
def c22 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked22 : check (branch ⟨true,true,4⟩) c22 = true := by decide
theorem child22 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,4⟩) c22 checked22 m hm)

/-! F0 move 23: NGram width 3, 28 states. -/
def c23 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked23 : check (branch ⟨true,true,5⟩) c23 = true := by decide
theorem child23 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,5⟩) c23 checked23 m hm)

theorem all_children (B : Nat) (hB : 128 ≤ B) (mv : Move) (m : Machine)
    (hm : compatible (branch mv) m) : WeightedBound B m := by
  rcases mv with ⟨w,d,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
    cases w <;> cases d <;>
    first
    | exact child0 B hB m (by simpa [branch] using hm)
    | exact child1 B hB m (by simpa [branch] using hm)
    | exact child2 B hB m (by simpa [branch] using hm)
    | exact child3 B hB m (by simpa [branch] using hm)
    | exact child4 B hB m (by simpa [branch] using hm)
    | exact child5 B hB m (by simpa [branch] using hm)
    | exact child6 B hB m (by simpa [branch] using hm)
    | exact child7 B hB m (by simpa [branch] using hm)
    | exact child8 B hB m (by simpa [branch] using hm)
    | exact child9 B hB m (by simpa [branch] using hm)
    | exact child10 B hB m (by simpa [branch] using hm)
    | exact child11 B hB m (by simpa [branch] using hm)
    | exact child12 B hB m (by simpa [branch] using hm)
    | exact child13 B hB m (by simpa [branch] using hm)
    | exact child14 B hB m (by simpa [branch] using hm)
    | exact child15 B hB m (by simpa [branch] using hm)
    | exact child16 B hB m (by simpa [branch] using hm)
    | exact child17 B hB m (by simpa [branch] using hm)
    | exact child18 B hB m (by simpa [branch] using hm)
    | exact child19 B hB m (by simpa [branch] using hm)
    | exact child20 B hB m (by simpa [branch] using hm)
    | exact child21 B hB m (by simpa [branch] using hm)
    | exact child22 B hB m (by simpa [branch] using hm)
    | exact child23 B hB m (by simpa [branch] using hm)

/-- Depth-six F412 A1=0RF completely bounded across all total
    completions, without assuming the champion clock. -/
theorem parent_sound (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (pA1 am) m) : WeightedBound B m := by
  apply split_at_hole B hB (pA1 am) (5,false) 11 (by decide)
    (pA1_root am) (pA1_F0_unknown am) (by decide) (by decide)
  · intro fm m' hc
    exact all_children B hB fm m' (by simpa [branch,pA1F0] using hc)
  · exact hm

#print axioms parent_sound
end BB6.Agent26F412Depth6.A10RF
