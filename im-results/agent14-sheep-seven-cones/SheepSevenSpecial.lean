import IndependentExceptionalGap
set_option maxRecDepth 32768

namespace SheepSevenSpecial

/-- All-k and all-source valuations: special odd-part-three predecessors impossible on all seven Sheep E cones. -/
theorem special_188_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(188+55080*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((188+55080*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (188+55080*k+0+0 - 2) (by omega) a
  have he : (188+55080*k+0+0 - 2)+2 = 188+55080*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_188_0_0

theorem special_188_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(188+55080*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((188+55080*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (188+55080*k+0+1 - 4) (by omega) a
  have he : (188+55080*k+0+1 - 4)+4 = 188+55080*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_188_0_1

theorem special_188_1_0 (k a : Nat) :
    153*2^a + 51*a + 257 ≠ 2^(188+55080*k+5+0) := by
  have h : 153*2^a + 51*a + 257 ≠ 2^((188+55080*k+5+0 - 8)+8) :=
    SheepIndependentGap.no_special_equal 153 51 257 7 103 2
      (by decide) (by decide) (by decide) (by decide)
      (188+55080*k+5+0 - 8) (by omega) a
  have he : (188+55080*k+5+0 - 8)+8 = 188+55080*k+5+0 := by omega
  simpa only [he] using h
#print axioms special_188_1_0

theorem special_188_1_1 (k a : Nat) :
    459*2^a + 153*a + 616 ≠ 2^(188+55080*k+5+1) := by
  have h : 459*2^a + 153*a + 616 ≠ 2^((188+55080*k+5+1 - 9)+9) :=
    SheepIndependentGap.no_special_equal 459 153 616 8 53 5
      (by decide) (by decide) (by decide) (by decide)
      (188+55080*k+5+1 - 9) (by omega) a
  have he : (188+55080*k+5+1 - 9)+9 = 188+55080*k+5+1 := by omega
  simpa only [he] using h
#print axioms special_188_1_1

theorem special_188_2_0 (k a : Nat) :
    765*2^a + 255*a + 1283 ≠ 2^(188+55080*k+7+0) := by
  have h : 765*2^a + 255*a + 1283 ≠ 2^((188+55080*k+7+0 - 10)+10) :=
    SheepIndependentGap.no_special_equal 765 255 1283 9 259 3
      (by decide) (by decide) (by decide) (by decide)
      (188+55080*k+7+0 - 10) (by omega) a
  have he : (188+55080*k+7+0 - 10)+10 = 188+55080*k+7+0 := by omega
  simpa only [he] using h
#print axioms special_188_2_0

theorem special_188_2_1 (k a : Nat) :
    2295*2^a + 765*a + 3076 ≠ 2^(188+55080*k+7+1) := by
  have h : 2295*2^a + 765*a + 3076 ≠ 2^((188+55080*k+7+1 - 12)+12) :=
    SheepIndependentGap.no_special_equal 2295 765 3076 11 1801 2
      (by decide) (by decide) (by decide) (by decide)
      (188+55080*k+7+1 - 12) (by omega) a
  have he : (188+55080*k+7+1 - 12)+12 = 188+55080*k+7+1 := by omega
  simpa only [he] using h
#print axioms special_188_2_1

theorem special_188_2_2 (k a : Nat) :
    6885*2^a + 2295*a + 7682 ≠ 2^(188+55080*k+7+2) := by
  have h : 6885*2^a + 2295*a + 7682 ≠ 2^((188+55080*k+7+2 - 13)+13) :=
    SheepIndependentGap.no_special_equal 6885 2295 7682 12 1307 4
      (by decide) (by decide) (by decide) (by decide)
      (188+55080*k+7+2 - 13) (by omega) a
  have he : (188+55080*k+7+2 - 13)+13 = 188+55080*k+7+2 := by omega
  simpa only [he] using h
#print axioms special_188_2_2

theorem special_190_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(190+306180*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((190+306180*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (190+306180*k+0+0 - 2) (by omega) a
  have he : (190+306180*k+0+0 - 2)+2 = 190+306180*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_190_0_0

theorem special_190_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(190+306180*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((190+306180*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (190+306180*k+0+1 - 4) (by omega) a
  have he : (190+306180*k+0+1 - 4)+4 = 190+306180*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_190_0_1

theorem special_190_1_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(190+306180*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((190+306180*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (190+306180*k+3+0 - 6) (by omega) a
  have he : (190+306180*k+3+0 - 6)+6 = 190+306180*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_190_1_0

theorem special_190_2_0 (k a : Nat) :
    405*2^a + 135*a + 601 ≠ 2^(190+306180*k+6+0) := by
  have h : 405*2^a + 135*a + 601 ≠ 2^((190+306180*k+6+0 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 601 8 107 4
      (by decide) (by decide) (by decide) (by decide)
      (190+306180*k+6+0 - 9) (by omega) a
  have he : (190+306180*k+6+0 - 9)+9 = 190+306180*k+6+0 := by omega
  simpa only [he] using h
#print axioms special_190_2_0

theorem special_190_3_0 (k a : Nat) :
    3645*2^a + 1215*a + 6833 ≠ 2^(190+306180*k+9+0) := by
  have h : 3645*2^a + 1215*a + 6833 ≠ 2^((190+306180*k+9+0 - 12)+12) :=
    SheepIndependentGap.no_special_equal 3645 1215 6833 11 451 5
      (by decide) (by decide) (by decide) (by decide)
      (190+306180*k+9+0 - 12) (by omega) a
  have he : (190+306180*k+9+0 - 12)+12 = 190+306180*k+9+0 := by omega
  simpa only [he] using h
#print axioms special_190_3_0

theorem special_190_3_1 (k a : Nat) :
    10935*2^a + 3645*a + 16096 ≠ 2^(190+306180*k+9+1) := by
  have h : 10935*2^a + 3645*a + 16096 ≠ 2^((190+306180*k+9+1 - 14)+14) :=
    SheepIndependentGap.no_special_equal 10935 3645 16096 13 5449 3
      (by decide) (by decide) (by decide) (by decide)
      (190+306180*k+9+1 - 14) (by omega) a
  have he : (190+306180*k+9+1 - 14)+14 = 190+306180*k+9+1 := by omega
  simpa only [he] using h
#print axioms special_190_3_1

theorem special_220_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(220+55080*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((220+55080*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (220+55080*k+0+0 - 2) (by omega) a
  have he : (220+55080*k+0+0 - 2)+2 = 220+55080*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_220_0_0

theorem special_220_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(220+55080*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((220+55080*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (220+55080*k+0+1 - 4) (by omega) a
  have he : (220+55080*k+0+1 - 4)+4 = 220+55080*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_220_0_1

theorem special_220_1_0 (k a : Nat) :
    153*2^a + 51*a + 257 ≠ 2^(220+55080*k+5+0) := by
  have h : 153*2^a + 51*a + 257 ≠ 2^((220+55080*k+5+0 - 8)+8) :=
    SheepIndependentGap.no_special_equal 153 51 257 7 103 2
      (by decide) (by decide) (by decide) (by decide)
      (220+55080*k+5+0 - 8) (by omega) a
  have he : (220+55080*k+5+0 - 8)+8 = 220+55080*k+5+0 := by omega
  simpa only [he] using h
#print axioms special_220_1_0

theorem special_220_2_0 (k a : Nat) :
    765*2^a + 255*a + 1283 ≠ 2^(220+55080*k+7+0) := by
  have h : 765*2^a + 255*a + 1283 ≠ 2^((220+55080*k+7+0 - 10)+10) :=
    SheepIndependentGap.no_special_equal 765 255 1283 9 259 3
      (by decide) (by decide) (by decide) (by decide)
      (220+55080*k+7+0 - 10) (by omega) a
  have he : (220+55080*k+7+0 - 10)+10 = 220+55080*k+7+0 := by omega
  simpa only [he] using h
#print axioms special_220_2_0

theorem special_220_3_0 (k a : Nat) :
    6885*2^a + 2295*a + 14089 ≠ 2^(220+55080*k+10+0) := by
  have h : 6885*2^a + 2295*a + 14089 ≠ 2^((220+55080*k+10+0 - 13)+13) :=
    SheepIndependentGap.no_special_equal 6885 2295 14089 12 1307 5
      (by decide) (by decide) (by decide) (by decide)
      (220+55080*k+10+0 - 13) (by omega) a
  have he : (220+55080*k+10+0 - 13)+13 = 220+55080*k+10+0 := by omega
  simpa only [he] using h
#print axioms special_220_3_0

theorem special_220_3_1 (k a : Nat) :
    20655*2^a + 6885*a + 32768 ≠ 2^(220+55080*k+10+1) := by
  have h : 20655*2^a + 6885*a + 32768 ≠ 2^((220+55080*k+10+1 - 15)+15) :=
    SheepIndependentGap.no_special_equal 20655 6885 32768 14 12113 2
      (by decide) (by decide) (by decide) (by decide)
      (220+55080*k+10+1 - 15) (by omega) a
  have he : (220+55080*k+10+1 - 15)+15 = 220+55080*k+10+1 := by omega
  simpa only [he] using h
#print axioms special_220_3_1

theorem special_262_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(262+53460*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((262+53460*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (262+53460*k+0+0 - 2) (by omega) a
  have he : (262+53460*k+0+0 - 2)+2 = 262+53460*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_262_0_0

theorem special_262_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(262+53460*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((262+53460*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (262+53460*k+0+1 - 4) (by omega) a
  have he : (262+53460*k+0+1 - 4)+4 = 262+53460*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_262_0_1

theorem special_262_1_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(262+53460*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((262+53460*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (262+53460*k+3+0 - 6) (by omega) a
  have he : (262+53460*k+3+0 - 6)+6 = 262+53460*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_262_1_0

theorem special_262_2_0 (k a : Nat) :
    405*2^a + 135*a + 601 ≠ 2^(262+53460*k+6+0) := by
  have h : 405*2^a + 135*a + 601 ≠ 2^((262+53460*k+6+0 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 601 8 107 4
      (by decide) (by decide) (by decide) (by decide)
      (262+53460*k+6+0 - 9) (by omega) a
  have he : (262+53460*k+6+0 - 9)+9 = 262+53460*k+6+0 := by omega
  simpa only [he] using h
#print axioms special_262_2_0

theorem special_262_3_0 (k a : Nat) :
    13365*2^a + 4455*a + 34757 ≠ 2^(262+53460*k+11+0) := by
  have h : 13365*2^a + 4455*a + 34757 ≠ 2^((262+53460*k+11+0 - 14)+14) :=
    SheepIndependentGap.no_special_equal 13365 4455 34757 13 3019 5
      (by decide) (by decide) (by decide) (by decide)
      (262+53460*k+11+0 - 14) (by omega) a
  have he : (262+53460*k+11+0 - 14)+14 = 262+53460*k+11+0 := by omega
  simpa only [he] using h
#print axioms special_262_3_0

theorem special_262_3_1 (k a : Nat) :
    40095*2^a + 13365*a + 78424 ≠ 2^(262+53460*k+11+1) := by
  have h : 40095*2^a + 13365*a + 78424 ≠ 2^((262+53460*k+11+1 - 16)+16) :=
    SheepIndependentGap.no_special_equal 40095 13365 78424 15 25441 3
      (by decide) (by decide) (by decide) (by decide)
      (262+53460*k+11+1 - 16) (by omega) a
  have he : (262+53460*k+11+1 - 16)+16 = 262+53460*k+11+1 := by omega
  simpa only [he] using h
#print axioms special_262_3_1

theorem special_442_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(442+1837080*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((442+1837080*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+0+0 - 2) (by omega) a
  have he : (442+1837080*k+0+0 - 2)+2 = 442+1837080*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_442_0_0

theorem special_442_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(442+1837080*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((442+1837080*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+0+1 - 4) (by omega) a
  have he : (442+1837080*k+0+1 - 4)+4 = 442+1837080*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_442_0_1

theorem special_442_1_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(442+1837080*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((442+1837080*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+3+0 - 6) (by omega) a
  have he : (442+1837080*k+3+0 - 6)+6 = 442+1837080*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_442_1_0

theorem special_442_2_0 (k a : Nat) :
    405*2^a + 135*a + 601 ≠ 2^(442+1837080*k+6+0) := by
  have h : 405*2^a + 135*a + 601 ≠ 2^((442+1837080*k+6+0 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 601 8 107 4
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+6+0 - 9) (by omega) a
  have he : (442+1837080*k+6+0 - 9)+9 = 442+1837080*k+6+0 := by omega
  simpa only [he] using h
#print axioms special_442_2_0

theorem special_442_2_1 (k a : Nat) :
    1215*2^a + 405*a + 1472 ≠ 2^(442+1837080*k+6+1) := by
  have h : 1215*2^a + 405*a + 1472 ≠ 2^((442+1837080*k+6+1 - 11)+11) :=
    SheepIndependentGap.no_special_equal 1215 405 1472 10 833 2
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+6+1 - 11) (by omega) a
  have he : (442+1837080*k+6+1 - 11)+11 = 442+1837080*k+6+1 := by omega
  simpa only [he] using h
#print axioms special_442_2_1

theorem special_442_2_2 (k a : Nat) :
    3645*2^a + 1215*a + 3754 ≠ 2^(442+1837080*k+6+2) := by
  have h : 3645*2^a + 1215*a + 3754 ≠ 2^((442+1837080*k+6+2 - 12)+12) :=
    SheepIndependentGap.no_special_equal 3645 1215 3754 11 451 5
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+6+2 - 12) (by omega) a
  have he : (442+1837080*k+6+2 - 12)+12 = 442+1837080*k+6+2 := by omega
  simpa only [he] using h
#print axioms special_442_2_2

theorem special_442_2_3 (k a : Nat) :
    10935*2^a + 3645*a + 9938 ≠ 2^(442+1837080*k+6+3) := by
  have h : 10935*2^a + 3645*a + 9938 ≠ 2^((442+1837080*k+6+3 - 14)+14) :=
    SheepIndependentGap.no_special_equal 10935 3645 9938 13 5449 2
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+6+3 - 14) (by omega) a
  have he : (442+1837080*k+6+3 - 14)+14 = 442+1837080*k+6+3 := by omega
  simpa only [he] using h
#print axioms special_442_2_3

theorem special_442_2_4 (k a : Nat) :
    32805*2^a + 10935*a + 27166 ≠ 2^(442+1837080*k+6+4) := by
  have h : 32805*2^a + 10935*a + 27166 ≠ 2^((442+1837080*k+6+4 - 16)+16) :=
    SheepIndependentGap.no_special_equal 32805 10935 27166 15 32731 1
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+6+4 - 16) (by omega) a
  have he : (442+1837080*k+6+4 - 16)+16 = 442+1837080*k+6+4 := by omega
  simpa only [he] using h
#print axioms special_442_2_4

theorem special_442_2_5 (k a : Nat) :
    98415*2^a + 32805*a + 76202 ≠ 2^(442+1837080*k+6+5) := by
  have h : 98415*2^a + 32805*a + 76202 ≠ 2^((442+1837080*k+6+5 - 17)+17) :=
    SheepIndependentGap.no_special_equal 98415 32805 76202 16 32657 3
      (by decide) (by decide) (by decide) (by decide)
      (442+1837080*k+6+5 - 17) (by omega) a
  have he : (442+1837080*k+6+5 - 17)+17 = 442+1837080*k+6+5 := by omega
  simpa only [he] using h
#print axioms special_442_2_5

theorem special_624_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(624+29160*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((624+29160*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (624+29160*k+0+0 - 2) (by omega) a
  have he : (624+29160*k+0+0 - 2)+2 = 624+29160*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_624_0_0

theorem special_624_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(624+29160*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((624+29160*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (624+29160*k+0+1 - 4) (by omega) a
  have he : (624+29160*k+0+1 - 4)+4 = 624+29160*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_624_0_1

theorem special_624_0_2 (k a : Nat) :
    27*2^a + 9*a + 22 ≠ 2^(624+29160*k+0+2) := by
  have h : 27*2^a + 9*a + 22 ≠ 2^((624+29160*k+0+2 - 5)+5) :=
    SheepIndependentGap.no_special_equal 27 9 22 4 5 4
      (by decide) (by decide) (by decide) (by decide)
      (624+29160*k+0+2 - 5) (by omega) a
  have he : (624+29160*k+0+2 - 5)+5 = 624+29160*k+0+2 := by omega
  simpa only [he] using h
#print axioms special_624_0_2

theorem special_624_1_0 (k a : Nat) :
    243*2^a + 81*a + 311 ≠ 2^(624+29160*k+5+0) := by
  have h : 243*2^a + 81*a + 311 ≠ 2^((624+29160*k+5+0 - 8)+8) :=
    SheepIndependentGap.no_special_equal 243 81 311 7 13 6
      (by decide) (by decide) (by decide) (by decide)
      (624+29160*k+5+0 - 8) (by omega) a
  have he : (624+29160*k+5+0 - 8)+8 = 624+29160*k+5+0 := by omega
  simpa only [he] using h
#print axioms special_624_1_0

theorem special_624_1_1 (k a : Nat) :
    729*2^a + 243*a + 784 ≠ 2^(624+29160*k+5+1) := by
  have h : 729*2^a + 243*a + 784 ≠ 2^((624+29160*k+5+1 - 10)+10) :=
    SheepIndependentGap.no_special_equal 729 243 784 9 295 3
      (by decide) (by decide) (by decide) (by decide)
      (624+29160*k+5+1 - 10) (by omega) a
  have he : (624+29160*k+5+1 - 10)+10 = 624+29160*k+5+1 := by omega
  simpa only [he] using h
#print axioms special_624_1_1

theorem special_624_2_0 (k a : Nat) :
    3645*2^a + 1215*a + 4351 ≠ 2^(624+29160*k+8+0) := by
  have h : 3645*2^a + 1215*a + 4351 ≠ 2^((624+29160*k+8+0 - 12)+12) :=
    SheepIndependentGap.no_special_equal 3645 1215 4351 11 451 5
      (by decide) (by decide) (by decide) (by decide)
      (624+29160*k+8+0 - 12) (by omega) a
  have he : (624+29160*k+8+0 - 12)+12 = 624+29160*k+8+0 := by omega
  simpa only [he] using h
#print axioms special_624_2_0

theorem special_648_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(648+122472*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((648+122472*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (648+122472*k+0+0 - 2) (by omega) a
  have he : (648+122472*k+0+0 - 2)+2 = 648+122472*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_648_0_0

theorem special_648_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(648+122472*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((648+122472*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (648+122472*k+0+1 - 4) (by omega) a
  have he : (648+122472*k+0+1 - 4)+4 = 648+122472*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_648_0_1

theorem special_648_0_2 (k a : Nat) :
    27*2^a + 9*a + 22 ≠ 2^(648+122472*k+0+2) := by
  have h : 27*2^a + 9*a + 22 ≠ 2^((648+122472*k+0+2 - 5)+5) :=
    SheepIndependentGap.no_special_equal 27 9 22 4 5 4
      (by decide) (by decide) (by decide) (by decide)
      (648+122472*k+0+2 - 5) (by omega) a
  have he : (648+122472*k+0+2 - 5)+5 = 648+122472*k+0+2 := by omega
  simpa only [he] using h
#print axioms special_648_0_2

theorem special_648_0_3 (k a : Nat) :
    81*2^a + 27*a + 62 ≠ 2^(648+122472*k+0+3) := by
  have h : 81*2^a + 27*a + 62 ≠ 2^((648+122472*k+0+3 - 7)+7) :=
    SheepIndependentGap.no_special_equal 81 27 62 6 47 1
      (by decide) (by decide) (by decide) (by decide)
      (648+122472*k+0+3 - 7) (by omega) a
  have he : (648+122472*k+0+3 - 7)+7 = 648+122472*k+0+3 := by omega
  simpa only [he] using h
#print axioms special_648_0_3

theorem special_648_0_4 (k a : Nat) :
    243*2^a + 81*a + 178 ≠ 2^(648+122472*k+0+4) := by
  have h : 243*2^a + 81*a + 178 ≠ 2^((648+122472*k+0+4 - 8)+8) :=
    SheepIndependentGap.no_special_equal 243 81 178 7 13 6
      (by decide) (by decide) (by decide) (by decide)
      (648+122472*k+0+4 - 8) (by omega) a
  have he : (648+122472*k+0+4 - 8)+8 = 648+122472*k+0+4 := by omega
  simpa only [he] using h
#print axioms special_648_0_4

theorem special_648_0_5 (k a : Nat) :
    729*2^a + 243*a + 518 ≠ 2^(648+122472*k+0+5) := by
  have h : 729*2^a + 243*a + 518 ≠ 2^((648+122472*k+0+5 - 10)+10) :=
    SheepIndependentGap.no_special_equal 729 243 518 9 295 2
      (by decide) (by decide) (by decide) (by decide)
      (648+122472*k+0+5 - 10) (by omega) a
  have he : (648+122472*k+0+5 - 10)+10 = 648+122472*k+0+5 := by omega
  simpa only [he] using h
#print axioms special_648_0_5

theorem special_648_1_0 (k a : Nat) :
    6561*2^a + 2187*a + 7789 ≠ 2^(648+122472*k+8+0) := by
  have h : 6561*2^a + 2187*a + 7789 ≠ 2^((648+122472*k+8+0 - 13)+13) :=
    SheepIndependentGap.no_special_equal 6561 2187 7789 12 1631 4
      (by decide) (by decide) (by decide) (by decide)
      (648+122472*k+8+0 - 13) (by omega) a
  have he : (648+122472*k+8+0 - 13)+13 = 648+122472*k+8+0 := by omega
  simpa only [he] using h
#print axioms special_648_1_0

end SheepSevenSpecial
