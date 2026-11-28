import F412ThreeHoleGeneric
import NGramCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth6.A10RFF03
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft BB6.Agent26F412ThreeHole BB6.Agent26F412TwoHole BB6.Agent1NGram

def am : Move := ⟨false,true,5⟩
def fm : Move := ⟨false,false,3⟩
def branch (mv : Move) : PartialMachine := pA1F0B1 am fm mv

/-! Certified width 1, 32 states. -/
def c0 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked0 : check (branch ⟨false,false,0⟩) c0 = true := by decide
theorem child0 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,0⟩) c0 checked0 m hm)

/-! Certified width 1, 32 states. -/
def c1 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked1 : check (branch ⟨false,false,1⟩) c1 = true := by decide
theorem child1 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,1⟩) c1 checked1 m hm)

/-! Certified width 1, 32 states. -/
def c2 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked2 : check (branch ⟨false,false,2⟩) c2 = true := by decide
theorem child2 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,2⟩) c2 checked2 m hm)

/-! Certified width 1, 30 states. -/
def c3 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked3 : check (branch ⟨false,false,3⟩) c3 = true := by decide
theorem child3 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,3⟩) c3 checked3 m hm)

/-! Certified width 7, 221 states. -/
def c4 : Cert := ⟨6,0xf30c00c00400f00000000000aa0000005104104004000000f3cc104055445555,0x4400000008000000000000000001440000000000054000005001055,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))))) .empty) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty (.branch .leaf (.branch .leaf .leaf)))))) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))))) .empty) .empty))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty)) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))))) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))))) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty (.branch .leaf .leaf))) .empty) .empty))) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))))) .empty))) .empty))) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty)) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty) .empty)) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))))) .empty))) (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))))))) (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))))))) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty)) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty .leaf)))) .empty) .empty)) .empty) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty (.branch .leaf .leaf)))) .empty) .empty)) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty)) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty) .empty)) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))))) .empty) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty (.branch .leaf (.branch .leaf .leaf)))))) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))))) .empty) .empty))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf))))) .empty) .empty) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty (.branch .leaf (.branch .leaf .leaf))))) .empty) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty))) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))) .empty) .empty) .empty))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty))) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty .leaf))))) .empty) .empty) .empty) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty (.branch .leaf .leaf))))) .empty) .empty) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty (.branch .leaf (.branch .leaf .leaf))))) .empty) .empty) .empty) .empty))) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty))) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty .leaf))))) .empty) .empty) .empty) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty (.branch .leaf .leaf))))) .empty) .empty) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch .leaf (.branch .leaf .leaf))))) .empty) .empty) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty))) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch .leaf (.branch .leaf .leaf))))))) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))))) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))))))) .empty))) .empty))]⟩
theorem checked4 : check (branch ⟨false,false,4⟩) c4 = true := by decide
theorem child4 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,4⟩) c4 checked4 m hm)

/-! Certified width 1, 30 states. -/
def c5 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked5 : check (branch ⟨false,false,5⟩) c5 = true := by decide
theorem child5 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,5⟩) c5 checked5 m hm)

/-! Certified width 1, 30 states. -/
def c6 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked6 : check (branch ⟨false,true,0⟩) c6 = true := by decide
theorem child6 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,0⟩) c6 checked6 m hm)

/-! Certified width 1, 32 states. -/
def c7 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked7 : check (branch ⟨false,true,1⟩) c7 = true := by decide
theorem child7 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,1⟩) c7 checked7 m hm)

/-! Certified width 1, 32 states. -/
def c8 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked8 : check (branch ⟨false,true,2⟩) c8 = true := by decide
theorem child8 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,2⟩) c8 checked8 m hm)

/-! Certified width 3, 43 states. -/
def c9 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked9 : check (branch ⟨false,true,3⟩) c9 = true := by decide
theorem child9 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,3⟩) c9 checked9 m hm)

/-! Final hole after 18 primitive steps. -/
theorem child10 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,4⟩) m) : WeightedBound B m :=
  pA1F0B1_short B hB am fm ⟨false,true,4⟩ 18 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 1, 30 states. -/
def c11 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked11 : check (branch ⟨false,true,5⟩) c11 = true := by decide
theorem child11 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,5⟩) c11 checked11 m hm)

/-! Certified width 1, 32 states. -/
def c12 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked12 : check (branch ⟨true,false,0⟩) c12 = true := by decide
theorem child12 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,0⟩) c12 checked12 m hm)

/-! Certified width 1, 30 states. -/
def c13 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked13 : check (branch ⟨true,false,1⟩) c13 = true := by decide
theorem child13 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,1⟩) c13 checked13 m hm)

/-! Certified width 1, 30 states. -/
def c14 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked14 : check (branch ⟨true,false,2⟩) c14 = true := by decide
theorem child14 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,2⟩) c14 checked14 m hm)

/-! Final hole after 19 primitive steps. -/
theorem child15 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,3⟩) m) : WeightedBound B m :=
  pA1F0B1_short B hB am fm ⟨true,false,3⟩ 19 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Final hole after 91 primitive steps. -/
theorem child16 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,4⟩) m) : WeightedBound B m :=
  pA1F0B1_short B hB am fm ⟨true,false,4⟩ 91 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 1, 30 states. -/
def c17 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked17 : check (branch ⟨true,false,5⟩) c17 = true := by decide
theorem child17 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,5⟩) c17 checked17 m hm)

/-! Certified width 1, 34 states. -/
def c18 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked18 : check (branch ⟨true,true,0⟩) c18 = true := by decide
theorem child18 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,0⟩) c18 checked18 m hm)

/-! Certified width 1, 30 states. -/
def c19 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked19 : check (branch ⟨true,true,1⟩) c19 = true := by decide
theorem child19 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,1⟩) c19 checked19 m hm)

/-! Certified width 1, 30 states. -/
def c20 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked20 : check (branch ⟨true,true,2⟩) c20 = true := by decide
theorem child20 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,2⟩) c20 checked20 m hm)

/-! Certified width 3, 33 states. -/
def c21 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked21 : check (branch ⟨true,true,3⟩) c21 = true := by decide
theorem child21 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,3⟩) c21 checked21 m hm)

/-! Final hole after 18 primitive steps. -/
theorem child22 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,4⟩) m) : WeightedBound B m :=
  pA1F0B1_short B hB am fm ⟨true,true,4⟩ 18 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 1, 30 states. -/
def c23 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
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

theorem parent_sound (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (pA1F0 am fm) m) : WeightedBound B m := by
  apply split_at_hole B hB (pA1F0 am fm) (1,true) 17 (by decide)
    (pA1F0_root am fm) (pA1F0_B1_unknown am fm) (by decide) (by decide)
  · intro mv m' hc
    exact all_children B hB mv m' (by simpa [branch, pA1F0B1] using hc)
  · exact hm

#print axioms parent_sound
end BB6.Agent26F412Depth6.A10RFF03
