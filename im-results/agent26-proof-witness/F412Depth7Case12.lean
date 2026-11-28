import F412TwoHoleGeneric
import NGramCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth7.Case12
open BB6Coverage BB6.Agent26F412Graft BB6.Agent26F412TwoHole BB6.Agent1NGram

def fm : Move := ⟨true,true,1⟩
def branch (mv : Move) : PartialMachine := pF0B1 fm mv

/-! Branch 0: window width 1, 28 abstract states. -/
def c0 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked0 : check (branch ⟨false,false,0⟩) c0 = true := by decide
theorem child0 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,0⟩) c0 checked0 m hm)

/-! Branch 1: window width 1, 28 abstract states. -/
def c1 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked1 : check (branch ⟨false,false,1⟩) c1 = true := by decide
theorem child1 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,1⟩) c1 checked1 m hm)

/-! Branch 2: window width 1, 28 abstract states. -/
def c2 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked2 : check (branch ⟨false,false,2⟩) c2 = true := by decide
theorem child2 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,2⟩) c2 checked2 m hm)

/-! Branch 3: window width 1, 26 abstract states. -/
def c3 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked3 : check (branch ⟨false,false,3⟩) c3 = true := by decide
theorem child3 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,3⟩) c3 checked3 m hm)

/-! Branch 4: remaining hole at primitive step 22. -/
theorem child4 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,4⟩) m) : WeightedBound B m :=
  pF0B1_short B hB fm ⟨false,false,4⟩ 22 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 5: window width 1, 28 abstract states. -/
def c5 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf))]⟩
theorem checked5 : check (branch ⟨false,false,5⟩) c5 = true := by decide
theorem child5 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,5⟩) c5 checked5 m hm)

/-! Branch 6: window width 1, 26 abstract states. -/
def c6 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked6 : check (branch ⟨false,true,0⟩) c6 = true := by decide
theorem child6 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,0⟩) c6 checked6 m hm)

/-! Branch 7: window width 1, 28 abstract states. -/
def c7 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked7 : check (branch ⟨false,true,1⟩) c7 = true := by decide
theorem child7 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,1⟩) c7 checked7 m hm)

/-! Branch 8: window width 1, 28 abstract states. -/
def c8 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked8 : check (branch ⟨false,true,2⟩) c8 = true := by decide
theorem child8 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,2⟩) c8 checked8 m hm)

/-! Branch 9: window width 9, 354 abstract states. -/
def c9 : Cert := ⟨8,0xffc0f000ff000000ffc0000000000000ffc0f000000000000000000000000000ffc0f000ff000000000000000000000000000000000000000000000000000000ffc0f000ff000000ffc0000000000000554050000000000000000000000000005540500055000000554000000000000055405000550000005540500055405555,0x40000000000000000000000000000000000000000000000000000004000000000000000000000000001000000000000040000004401455,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty)))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty))) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))))) .empty) .empty) .empty) .empty))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty))) (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)))) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))))) .empty) .empty) .empty))) .empty))) .empty)),(.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))))) .empty) .empty) .empty))) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty))) .empty)) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty)))) .empty)) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch .leaf .leaf)))) .empty))) .empty)) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))) .empty))) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))))) .empty)) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))) (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))))))) .empty))) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty))) .empty)) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty))) (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) .empty)))) .empty)) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))) .empty))) .empty) .empty) .empty) .empty))) .empty))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty))) .empty) (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty))) .empty)) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)))) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))))) .empty) (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))))) .empty)) .empty) .empty) .empty))) .empty))) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty))) .empty))) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)))) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))) .empty))) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) (.branch (.branch .leaf (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))))))) .empty) .empty))) .empty))) .empty))]⟩
theorem checked9 : check (branch ⟨false,true,3⟩) c9 = true := by decide
theorem child9 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,3⟩) c9 checked9 m hm)

/-! Branch 10: remaining hole at primitive step 17. -/
theorem child10 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,4⟩) m) : WeightedBound B m :=
  pF0B1_short B hB fm ⟨false,true,4⟩ 17 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 11: window width 1, 30 abstract states. -/
def c11 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf))]⟩
theorem checked11 : check (branch ⟨false,true,5⟩) c11 = true := by decide
theorem child11 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,5⟩) c11 checked11 m hm)

/-! Branch 12: window width 1, 28 abstract states. -/
def c12 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf (.branch .leaf .leaf)),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked12 : check (branch ⟨true,false,0⟩) c12 = true := by decide
theorem child12 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,0⟩) c12 checked12 m hm)

/-! Branch 13: window width 1, 26 abstract states. -/
def c13 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked13 : check (branch ⟨true,false,1⟩) c13 = true := by decide
theorem child13 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,1⟩) c13 checked13 m hm)

/-! Branch 14: window width 1, 26 abstract states. -/
def c14 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked14 : check (branch ⟨true,false,2⟩) c14 = true := by decide
theorem child14 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,2⟩) c14 checked14 m hm)

/-! Branch 15: remaining hole at primitive step 18. -/
theorem child15 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,3⟩) m) : WeightedBound B m :=
  pF0B1_short B hB fm ⟨true,false,3⟩ 18 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 16: remaining hole at primitive step 32. -/
theorem child16 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,4⟩) m) : WeightedBound B m :=
  pF0B1_short B hB fm ⟨true,false,4⟩ 32 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 17: window width 1, 28 abstract states. -/
def c17 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf))]⟩
theorem checked17 : check (branch ⟨true,false,5⟩) c17 = true := by decide
theorem child17 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,5⟩) c17 checked17 m hm)

/-! Branch 18: window width 1, 30 abstract states. -/
def c18 : Cert := ⟨0,0xf,0xf,#[(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked18 : check (branch ⟨true,true,0⟩) c18 = true := by decide
theorem child18 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,0⟩) c18 checked18 m hm)

/-! Branch 19: window width 1, 26 abstract states. -/
def c19 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked19 : check (branch ⟨true,true,1⟩) c19 = true := by decide
theorem child19 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,1⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,1⟩) c19 checked19 m hm)

/-! Branch 20: window width 1, 26 abstract states. -/
def c20 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
theorem checked20 : check (branch ⟨true,true,2⟩) c20 = true := by decide
theorem child20 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,2⟩) c20 checked20 m hm)

/-! Branch 21: window width 3, 17 abstract states. -/
def c21 : Cert := ⟨2,0x4495,0x455,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) .leaf),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty),(.branch .empty .leaf),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))]⟩
theorem checked21 : check (branch ⟨true,true,3⟩) c21 = true := by decide
theorem child21 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,3⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,3⟩) c21 checked21 m hm)

/-! Branch 22: remaining hole at primitive step 17. -/
theorem child22 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,4⟩) m) : WeightedBound B m :=
  pF0B1_short B hB fm ⟨true,true,4⟩ 17 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 23: window width 1, 26 abstract states. -/
def c23 : Cert := ⟨0,0xf,0xf,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf))]⟩
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

/-- Exact closure of all F0=1RB completions. -/
theorem parent_sound (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (pF0 fm) m) : WeightedBound B m := by
  apply split_at_hole B hB (pF0 fm) (1,true) 16 (by decide)
    (pF0_root fm) (pF0_B1_unknown fm) (by decide) (by decide)
  · intro mv m' hc
    exact all_children B hB mv m' (by simpa [branch, pF0B1] using hc)
  · exact hm

#print axioms parent_sound
end BB6.Agent26F412Depth7.Case12
