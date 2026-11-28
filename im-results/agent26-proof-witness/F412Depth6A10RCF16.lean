import F412ThreeHoleGeneric
import NGramCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth6.A10RCF16
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft BB6.Agent26F412ThreeHole BB6.Agent26F412TwoHole BB6.Agent1NGram

def am : Move := ⟨false,true,2⟩
def fm : Move := ⟨true,false,4⟩
def branch (mv : Move) : PartialMachine := pA1F0E1 am fm mv

/-! Final hole after 34 primitive steps. -/
theorem child0 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,0⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨false,false,0⟩ 34 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Final hole after 18 primitive steps. -/
theorem child1 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,1⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨false,false,1⟩ 18 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 5, 116 states. -/
def c2 : Cert := ⟨4,0xf30c00f05504ff55,0x140000014005155,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))) .empty) .empty))) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))) .empty)))) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty) .empty) .empty)))]⟩
theorem checked2 : check (branch ⟨false,false,2⟩) c2 = true := by decide
theorem child2 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,2⟩) c2 checked2 m hm)

/-! Certified width 3, 28 states. -/
def c3 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked3 : check (branch ⟨false,false,3⟩) c3 = true := by decide
theorem child3 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,3⟩) c3 checked3 m hm)

/-! Final hole after 40 primitive steps. -/
theorem child4 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,4⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨false,false,4⟩ 40 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Final hole after 18 primitive steps. -/
theorem child5 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,5⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨false,false,5⟩ 18 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 3, 37 states. -/
def c6 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked6 : check (branch ⟨false,true,0⟩) c6 = true := by decide
theorem child6 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,0⟩) c6 checked6 m hm)

/-! Final hole after 14 primitive steps. -/
theorem child7 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,1⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨false,true,1⟩ 14 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 3, 48 states. -/
def c8 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked8 : check (branch ⟨false,true,2⟩) c8 = true := by decide
theorem child8 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,2⟩) c8 checked8 m hm)

/-! Certified width 3, 35 states. -/
def c9 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked9 : check (branch ⟨false,true,3⟩) c9 = true := by decide
theorem child9 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,3⟩) c9 checked9 m hm)

/-! Certified width 3, 43 states. -/
def c10 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked10 : check (branch ⟨false,true,4⟩) c10 = true := by decide
theorem child10 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,4⟩) c10 checked10 m hm)

/-! Certified width 3, 36 states. -/
def c11 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .leaf (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked11 : check (branch ⟨false,true,5⟩) c11 = true := by decide
theorem child11 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,5⟩) c11 checked11 m hm)

/-! Final hole after 15 primitive steps. -/
theorem child12 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,0⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨true,false,0⟩ 15 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Final hole after 24 primitive steps. -/
theorem child13 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,1⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨true,false,1⟩ 24 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 3, 32 states. -/
def c14 : Cert := ⟨2,0xfffd,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked14 : check (branch ⟨true,false,2⟩) c14 = true := by decide
theorem child14 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,2⟩) c14 checked14 m hm)

/-! Certified width 3, 31 states. -/
def c15 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked15 : check (branch ⟨true,false,3⟩) c15 = true := by decide
theorem child15 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,3⟩) c15 checked15 m hm)

/-! Final hole after 30 primitive steps. -/
theorem child16 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,4⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨true,false,4⟩ 30 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Final hole after 18 primitive steps. -/
theorem child17 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,5⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨true,false,5⟩ 18 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 3, 34 states. -/
def c18 : Cert := ⟨2,0xf7fd,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked18 : check (branch ⟨true,true,0⟩) c18 = true := by decide
theorem child18 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,0⟩) c18 checked18 m hm)

/-! Final hole after 14 primitive steps. -/
theorem child19 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,1⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨true,true,1⟩ 14 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 3, 28 states. -/
def c20 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked20 : check (branch ⟨true,true,2⟩) c20 = true := by decide
theorem child20 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,2⟩) c20 checked20 m hm)

/-! Final hole after 15 primitive steps. -/
theorem child21 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,3⟩) m) : WeightedBound B m :=
  pA1F0E1_short B hB am fm ⟨true,true,3⟩ 15 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Certified width 3, 36 states. -/
def c22 : Cert := ⟨2,0xf35d,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))]⟩
theorem checked22 : check (branch ⟨true,true,4⟩) c22 = true := by decide
theorem child22 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,4⟩) c22 checked22 m hm)

/-! Certified width 4, 60 states. -/
def c23 : Cert := ⟨3,0xf30c55f5,0x401455,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty) .empty)) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch .leaf (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))))) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty) .empty))),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty) .empty))),(.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) .empty)) .empty))]⟩
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
  apply split_at_hole B hB (pA1F0 am fm) (4,true) 13 (by decide)
    (pA1F0_root am fm) (pA1F0_E1_unknown am fm) (by decide) (by decide)
  · intro mv m' hc
    exact all_children B hB mv m' (by simpa [branch, pA1F0E1] using hc)
  · exact hm

#print axioms parent_sound
end BB6.Agent26F412Depth6.A10RCF16
