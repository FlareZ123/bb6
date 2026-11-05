import IndependentGenericHigh
set_option maxRecDepth 32768

namespace SheepSevenGenericHigh

/-- Uniform generic inverse remainder bounds for all seven Sheep E inverse cones. -/
theorem high_188_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_188_0_0

theorem high_188_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_188_0_1

theorem high_188_1_0 (a : Nat) (ha : 11 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 51 (-104:Int) a ∧
    SheepIndependentGenericHigh.K 51 (-104:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 51 (-104:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    51 11 (-104:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_188_1_0

theorem high_188_1_1 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 153 (-157:Int) a ∧
    SheepIndependentGenericHigh.K 153 (-157:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 153 (-157:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    153 12 (-157:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_188_1_1

theorem high_188_2_0 (a : Nat) (ha : 13 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 255 (-518:Int) a ∧
    SheepIndependentGenericHigh.K 255 (-518:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 255 (-518:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    255 13 (-518:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_188_2_0

theorem high_188_2_1 (a : Nat) (ha : 15 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 765 (-781:Int) a ∧
    SheepIndependentGenericHigh.K 765 (-781:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 765 (-781:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    765 15 (-781:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_188_2_1

theorem high_188_2_2 (a : Nat) (ha : 17 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 2295 (-797:Int) a ∧
    SheepIndependentGenericHigh.K 2295 (-797:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 2295 (-797:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    2295 17 (-797:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_188_2_2

theorem high_190_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_190_0_0

theorem high_190_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_190_0_1

theorem high_190_1_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_190_1_0

theorem high_190_2_0 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (-196:Int) a ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (-196:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_190_2_0

theorem high_190_3_0 (a : Nat) (ha : 16 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1215 (-3188:Int) a ∧
    SheepIndependentGenericHigh.K 1215 (-3188:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1215 (-3188:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1215 16 (-3188:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_190_3_0

theorem high_190_3_1 (a : Nat) (ha : 17 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3645 (-5161:Int) a ∧
    SheepIndependentGenericHigh.K 3645 (-5161:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3645 (-5161:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3645 17 (-5161:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_190_3_1

theorem high_220_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_220_0_0

theorem high_220_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_220_0_1

theorem high_220_1_0 (a : Nat) (ha : 11 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 51 (-104:Int) a ∧
    SheepIndependentGenericHigh.K 51 (-104:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 51 (-104:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    51 11 (-104:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_220_1_0

theorem high_220_2_0 (a : Nat) (ha : 13 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 255 (-518:Int) a ∧
    SheepIndependentGenericHigh.K 255 (-518:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 255 (-518:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    255 13 (-518:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_220_2_0

theorem high_220_3_0 (a : Nat) (ha : 17 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 2295 (-7204:Int) a ∧
    SheepIndependentGenericHigh.K 2295 (-7204:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 2295 (-7204:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    2295 17 (-7204:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_220_3_0

theorem high_220_3_1 (a : Nat) (ha : 19 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 6885 (-12113:Int) a ∧
    SheepIndependentGenericHigh.K 6885 (-12113:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 6885 (-12113:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    6885 19 (-12113:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_220_3_1

theorem high_262_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_262_0_0

theorem high_262_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_262_0_1

theorem high_262_1_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_262_1_0

theorem high_262_2_0 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (-196:Int) a ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (-196:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_262_2_0

theorem high_262_3_0 (a : Nat) (ha : 18 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 4455 (-21392:Int) a ∧
    SheepIndependentGenericHigh.K 4455 (-21392:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 4455 (-21392:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    4455 18 (-21392:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_262_3_0

theorem high_262_3_1 (a : Nat) (ha : 20 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 13365 (-38329:Int) a ∧
    SheepIndependentGenericHigh.K 13365 (-38329:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 13365 (-38329:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    13365 20 (-38329:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_262_3_1

theorem high_442_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_0_0

theorem high_442_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_0_1

theorem high_442_1_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_1_0

theorem high_442_2_0 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (-196:Int) a ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (-196:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_2_0

theorem high_442_2_1 (a : Nat) (ha : 14 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 405 (-257:Int) a ∧
    SheepIndependentGenericHigh.K 405 (-257:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 405 (-257:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    405 14 (-257:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_2_1

theorem high_442_2_2 (a : Nat) (ha : 16 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1215 (-109:Int) a ∧
    SheepIndependentGenericHigh.K 1215 (-109:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1215 (-109:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1215 16 (-109:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_2_2

theorem high_442_2_3 (a : Nat) (ha : 17 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3645 (997:Int) a ∧
    SheepIndependentGenericHigh.K 3645 (997:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3645 (997:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3645 17 (997:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_2_3

theorem high_442_2_4 (a : Nat) (ha : 19 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 10935 (5639:Int) a ∧
    SheepIndependentGenericHigh.K 10935 (5639:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 10935 (5639:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    10935 19 (5639:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_2_4

theorem high_442_2_5 (a : Nat) (ha : 21 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 32805 (22213:Int) a ∧
    SheepIndependentGenericHigh.K 32805 (22213:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 32805 (22213:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    32805 21 (22213:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_442_2_5

theorem high_624_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_624_0_0

theorem high_624_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_624_0_1

theorem high_624_0_2 (a : Nat) (ha : 7 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 9 (5:Int) a ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    9 7 (5:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_624_0_2

theorem high_624_1_0 (a : Nat) (ha : 11 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 81 (-68:Int) a ∧
    SheepIndependentGenericHigh.K 81 (-68:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 81 (-68:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    81 11 (-68:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_624_1_0

theorem high_624_1_1 (a : Nat) (ha : 13 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 243 (-55:Int) a ∧
    SheepIndependentGenericHigh.K 243 (-55:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 243 (-55:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    243 13 (-55:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_624_1_1

theorem high_624_2_0 (a : Nat) (ha : 16 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1215 (-706:Int) a ∧
    SheepIndependentGenericHigh.K 1215 (-706:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1215 (-706:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1215 16 (-706:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_624_2_0

theorem high_648_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_648_0_0

theorem high_648_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_648_0_1

theorem high_648_0_2 (a : Nat) (ha : 7 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 9 (5:Int) a ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    9 7 (5:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_648_0_2

theorem high_648_0_3 (a : Nat) (ha : 9 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 27 (19:Int) a ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    27 9 (19:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_648_0_3

theorem high_648_0_4 (a : Nat) (ha : 11 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 81 (65:Int) a ∧
    SheepIndependentGenericHigh.K 81 (65:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 81 (65:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    81 11 (65:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_648_0_4

theorem high_648_0_5 (a : Nat) (ha : 13 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 243 (211:Int) a ∧
    SheepIndependentGenericHigh.K 243 (211:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 243 (211:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    243 13 (211:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_648_0_5

theorem high_648_1_0 (a : Nat) (ha : 17 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 2187 (-1228:Int) a ∧
    SheepIndependentGenericHigh.K 2187 (-1228:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 2187 (-1228:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    2187 17 (-1228:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_648_1_0

end SheepSevenGenericHigh
