import F412TwoHoleGeneric
import NGramCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Depth7.Case10
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent26F412Graft BB6.Agent26F412TwoHole BB6.Agent1NGram

def fm : Move := ⟨true,false,4⟩
def branch (mv : Move) : PartialMachine := pF0E1 fm mv

/-! Branch 0: remaining hole at primitive step 40. -/
theorem child0 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,0⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨false,false,0⟩ 40 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 1: remaining hole at primitive step 14. -/
theorem child1 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,1⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨false,false,1⟩ 14 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 2: remaining hole at primitive step 42. -/
theorem child2 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,2⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨false,false,2⟩ 42 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 3: remaining hole at primitive step 28. -/
theorem child3 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,3⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨false,false,3⟩ 28 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 4: window width 4, 48 abstract states. -/
def c4 : Cert := ⟨3,0x404455,0xffa2f355,#[.leaf,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf),(.branch (.branch .empty .leaf) .empty),.leaf,(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) .leaf),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .leaf .leaf))))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))))),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))]⟩
theorem checked4 : check (branch ⟨false,false,4⟩) c4 = true := by decide
theorem child4 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,false,4⟩) c4 checked4 m hm)

/-! Branch 5: remaining hole at primitive step 16. -/
theorem child5 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,false,5⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨false,false,5⟩ 16 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 6: window width 3, 14 abstract states. -/
def c6 : Cert := ⟨2,0x4b5,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),(.branch (.branch .empty .leaf) .empty),.leaf,(.branch .empty .leaf),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))]⟩
theorem checked6 : check (branch ⟨false,true,0⟩) c6 = true := by decide
theorem child6 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,0⟩) c6 checked6 m hm)

/-! Branch 7: remaining hole at primitive step 14. -/
theorem child7 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,1⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨false,true,1⟩ 14 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 8: window width 3, 18 abstract states. -/
def c8 : Cert := ⟨2,0x4b5,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .leaf),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .leaf) .empty),.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))]⟩
theorem checked8 : check (branch ⟨false,true,2⟩) c8 = true := by decide
theorem child8 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,2⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,2⟩) c8 checked8 m hm)

/-! Branch 9: remaining hole at primitive step 34. -/
theorem child9 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,3⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨false,true,3⟩ 34 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 10: window width 3, 27 abstract states. -/
def c10 : Cert := ⟨2,0x1dfd,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty))]⟩
theorem checked10 : check (branch ⟨false,true,4⟩) c10 = true := by decide
theorem child10 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,4⟩) c10 checked10 m hm)

/-! Branch 11: window width 3, 26 abstract states. -/
def c11 : Cert := ⟨2,0x1dfd,0x55,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty))]⟩
theorem checked11 : check (branch ⟨false,true,5⟩) c11 = true := by decide
theorem child11 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨false,true,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨false,true,5⟩) c11 checked11 m hm)

/-! Branch 12: remaining hole at primitive step 30. -/
theorem child12 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,0⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,false,0⟩ 30 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 13: remaining hole at primitive step 14. -/
theorem child13 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,1⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,false,1⟩ 14 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 14: remaining hole at primitive step 32. -/
theorem child14 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,2⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,false,2⟩ 32 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 15: remaining hole at primitive step 46. -/
theorem child15 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,3⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,false,3⟩ 46 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 16: remaining hole at primitive step 18. -/
theorem child16 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,4⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,false,4⟩ 18 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 17: window width 3, 41 abstract states. -/
def c17 : Cert := ⟨2,0xffff,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty)),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)))]⟩
theorem checked17 : check (branch ⟨true,false,5⟩) c17 = true := by decide
theorem child17 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,false,5⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,false,5⟩) c17 checked17 m hm)

/-! Branch 18: window width 3, 20 abstract states. -/
def c18 : Cert := ⟨2,0xc495,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),(.branch (.branch .empty .leaf) .empty),.leaf,(.branch .empty .leaf),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))]⟩
theorem checked18 : check (branch ⟨true,true,0⟩) c18 = true := by decide
theorem child18 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,0⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,0⟩) c18 checked18 m hm)

/-! Branch 19: remaining hole at primitive step 14. -/
theorem child19 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,1⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,true,1⟩ 14 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 20: remaining hole at primitive step 16. -/
theorem child20 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,2⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,true,2⟩ 16 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 21: remaining hole at primitive step 15. -/
theorem child21 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,3⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,true,3⟩ 15 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

/-! Branch 22: window width 3, 21 abstract states. -/
def c22 : Cert := ⟨2,0xc495,0x55,#[.leaf,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf),(.branch (.branch .empty .leaf) .empty),.leaf,(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) .leaf),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))]⟩
theorem checked22 : check (branch ⟨true,true,4⟩) c22 = true := by decide
theorem child22 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,4⟩) m) : WeightedBound B m :=
  weighted_never B m (never (branch ⟨true,true,4⟩) c22 checked22 m hm)

/-! Branch 23: remaining hole at primitive step 38. -/
theorem child23 (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (branch ⟨true,true,5⟩) m) : WeightedBound B m :=
  pF0E1_short B hB fm ⟨true,true,5⟩ 38 (by decide) (by decide) (by decide) m
    (by simpa [branch] using hm)

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

/-- Exact closure of all F0=1LE completions. -/
theorem parent_sound (B : Nat) (hB : 128 ≤ B) (m : Machine)
    (hm : compatible (pF0 fm) m) : WeightedBound B m := by
  apply split_at_hole B hB (pF0 fm) (4,true) 13 (by decide)
    (pF0_root fm) (pF0_E1_unknown fm) (by decide) (by decide)
  · intro mv m' hc
    exact all_children B hB mv m' (by simpa [branch, pF0E1] using hc)
  · exact hm

#print axioms parent_sound
end BB6.Agent26F412Depth7.Case10
