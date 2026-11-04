import IndependentGenericHigh
set_option maxRecDepth 32768

namespace SheepFiveGenericHigh

/-- Inductive high-valuation congruence remainder bounds for all 44 rows. -/
theorem high_118_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_118_0_0

theorem high_118_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_118_0_1

theorem high_118_1_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_118_1_0

theorem high_118_2_0 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (-196:Int) a ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (-196:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (-196:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_118_2_0

theorem high_118_2_1 (a : Nat) (ha : 14 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 405 (-257:Int) a ∧
    SheepIndependentGenericHigh.K 405 (-257:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 405 (-257:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    405 14 (-257:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_118_2_1

theorem high_118_2_2 (a : Nat) (ha : 16 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1215 (-109:Int) a ∧
    SheepIndependentGenericHigh.K 1215 (-109:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1215 (-109:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1215 16 (-109:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_118_2_2

theorem high_246_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_0_0

theorem high_246_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_0_1

theorem high_246_0_2 (a : Nat) (ha : 7 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 9 (5:Int) a ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    9 7 (5:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_0_2

theorem high_246_1_0 (a : Nat) (ha : 11 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 81 (-68:Int) a ∧
    SheepIndependentGenericHigh.K 81 (-68:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 81 (-68:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    81 11 (-68:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_1_0

theorem high_246_2_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_2_0

theorem high_246_2_1 (a : Nat) (ha : 10 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 45 (11:Int) a ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    45 10 (11:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_2_1

theorem high_246_2_2 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (67:Int) a ∧
    SheepIndependentGenericHigh.K 135 (67:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (67:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (67:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_2_2

theorem high_246_2_3 (a : Nat) (ha : 14 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 405 (269:Int) a ∧
    SheepIndependentGenericHigh.K 405 (269:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 405 (269:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    405 14 (269:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_2_3

theorem high_246_3_0 (a : Nat) (ha : 16 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 2025 (266:Int) a ∧
    SheepIndependentGenericHigh.K 2025 (266:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 2025 (266:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    2025 16 (266:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_3_0

theorem high_246_4_0 (a : Nat) (ha : 13 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 225 (-46:Int) a ∧
    SheepIndependentGenericHigh.K 225 (-46:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 225 (-46:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    225 13 (-46:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_4_0

theorem high_246_4_1 (a : Nat) (ha : 15 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 675 (133:Int) a ∧
    SheepIndependentGenericHigh.K 675 (133:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 675 (133:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    675 15 (133:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_246_4_1

theorem high_558_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_0_0

theorem high_558_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_0_1

theorem high_558_0_2 (a : Nat) (ha : 7 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 9 (5:Int) a ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    9 7 (5:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_0_2

theorem high_558_0_3 (a : Nat) (ha : 9 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 27 (19:Int) a ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    27 9 (19:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_0_3

theorem high_558_1_0 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (22:Int) a ∧
    SheepIndependentGenericHigh.K 135 (22:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (22:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (22:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_1_0

theorem high_558_2_0 (a : Nat) (ha : 15 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 675 (-182:Int) a ∧
    SheepIndependentGenericHigh.K 675 (-182:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 675 (-182:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    675 15 (-182:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_2_0

theorem high_558_3_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_3_0

theorem high_558_3_1 (a : Nat) (ha : 10 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 45 (11:Int) a ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    45 10 (11:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_558_3_1

theorem high_846_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_0_0

theorem high_846_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_0_1

theorem high_846_0_2 (a : Nat) (ha : 7 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 9 (5:Int) a ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    9 7 (5:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_0_2

theorem high_846_0_3 (a : Nat) (ha : 9 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 27 (19:Int) a ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    27 9 (19:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_0_3

theorem high_846_1_0 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (22:Int) a ∧
    SheepIndependentGenericHigh.K 135 (22:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (22:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (22:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_1_0

theorem high_846_2_0 (a : Nat) (ha : 19 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 8775 (-37472:Int) a ∧
    SheepIndependentGenericHigh.K 8775 (-37472:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 8775 (-37472:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    8775 19 (-37472:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_2_0

theorem high_846_3_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_3_0

theorem high_846_3_1 (a : Nat) (ha : 10 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 45 (11:Int) a ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    45 10 (11:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_3_1

theorem high_846_4_0 (a : Nat) (ha : 13 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 225 (-46:Int) a ∧
    SheepIndependentGenericHigh.K 225 (-46:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 225 (-46:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    225 13 (-46:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_846_4_0

theorem high_702_0_0 (a : Nat) (ha : 2 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 1 (0:Int) a ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 1 (0:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    1 2 (0:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_0_0

theorem high_702_0_1 (a : Nat) (ha : 5 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 3 (1:Int) a ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 3 (1:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    3 5 (1:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_0_1

theorem high_702_0_2 (a : Nat) (ha : 7 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 9 (5:Int) a ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 9 (5:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    9 7 (5:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_0_2

theorem high_702_0_3 (a : Nat) (ha : 9 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 27 (19:Int) a ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 27 (19:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    27 9 (19:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_0_3

theorem high_702_0_4 (a : Nat) (ha : 11 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 81 (65:Int) a ∧
    SheepIndependentGenericHigh.K 81 (65:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 81 (65:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    81 11 (65:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_0_4

theorem high_702_1_0 (a : Nat) (ha : 12 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 135 (22:Int) a ∧
    SheepIndependentGenericHigh.K 135 (22:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 135 (22:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    135 12 (22:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_1_0

theorem high_702_1_1 (a : Nat) (ha : 14 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 405 (179:Int) a ∧
    SheepIndependentGenericHigh.K 405 (179:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 405 (179:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    405 14 (179:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_1_1

theorem high_702_2_0 (a : Nat) (ha : 8 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 15 (-2:Int) a ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 15 (-2:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    15 8 (-2:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_2_0

theorem high_702_2_1 (a : Nat) (ha : 10 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 45 (11:Int) a ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 45 (11:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    45 10 (11:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_2_1

theorem high_702_3_0 (a : Nat) (ha : 14 ≤ a) :
    (1:Int)<SheepIndependentGenericHigh.K 405 (-452:Int) a ∧
    SheepIndependentGenericHigh.K 405 (-452:Int) a % 2 = 1 ∧
    SheepIndependentGenericHigh.K 405 (-452:Int) a < (2:Int)^a := by
  obtain ⟨hlo,hodd,hupper,_⟩ := SheepIndependentGenericHigh.high_all
    405 14 (-452:Int) (by decide) a ha
  exact ⟨hlo,hodd,hupper⟩
#print axioms high_702_3_0

end SheepFiveGenericHigh
