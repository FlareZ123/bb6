import IndependentExceptionalGap
set_option maxRecDepth 32768

namespace SheepFiveSpecial

/-- Universal quantified exceptional inverse certificates from a checked base gap. -/
theorem special_118_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(118+14580*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((118+14580*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (118+14580*k+0+0 - 2) (by omega) a
  have he : (118+14580*k+0+0 - 2)+2 = 118+14580*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_118_0_0

theorem special_118_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(118+14580*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((118+14580*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (118+14580*k+0+1 - 4) (by omega) a
  have he : (118+14580*k+0+1 - 4)+4 = 118+14580*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_118_0_1

theorem special_118_1_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(118+14580*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((118+14580*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (118+14580*k+3+0 - 6) (by omega) a
  have he : (118+14580*k+3+0 - 6)+6 = 118+14580*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_118_1_0

theorem special_118_2_0 (k a : Nat) :
    405*2^a + 135*a + 601 ≠ 2^(118+14580*k+6+0) := by
  have h : 405*2^a + 135*a + 601 ≠ 2^((118+14580*k+6+0 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 601 8 107 4
      (by decide) (by decide) (by decide) (by decide)
      (118+14580*k+6+0 - 9) (by omega) a
  have he : (118+14580*k+6+0 - 9)+9 = 118+14580*k+6+0 := by omega
  simpa only [he] using h
#print axioms special_118_2_0

theorem special_118_2_1 (k a : Nat) :
    1215*2^a + 405*a + 1472 ≠ 2^(118+14580*k+6+1) := by
  have h : 1215*2^a + 405*a + 1472 ≠ 2^((118+14580*k+6+1 - 11)+11) :=
    SheepIndependentGap.no_special_equal 1215 405 1472 10 833 2
      (by decide) (by decide) (by decide) (by decide)
      (118+14580*k+6+1 - 11) (by omega) a
  have he : (118+14580*k+6+1 - 11)+11 = 118+14580*k+6+1 := by omega
  simpa only [he] using h
#print axioms special_118_2_1

theorem special_118_2_2 (k a : Nat) :
    3645*2^a + 1215*a + 3754 ≠ 2^(118+14580*k+6+2) := by
  have h : 3645*2^a + 1215*a + 3754 ≠ 2^((118+14580*k+6+2 - 12)+12) :=
    SheepIndependentGap.no_special_equal 3645 1215 3754 11 451 5
      (by decide) (by decide) (by decide) (by decide)
      (118+14580*k+6+2 - 12) (by omega) a
  have he : (118+14580*k+6+2 - 12)+12 = 118+14580*k+6+2 := by omega
  simpa only [he] using h
#print axioms special_118_2_2

theorem special_246_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(246+24300*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((246+24300*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+0+0 - 2) (by omega) a
  have he : (246+24300*k+0+0 - 2)+2 = 246+24300*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_246_0_0

theorem special_246_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(246+24300*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((246+24300*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+0+1 - 4) (by omega) a
  have he : (246+24300*k+0+1 - 4)+4 = 246+24300*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_246_0_1

theorem special_246_0_2 (k a : Nat) :
    27*2^a + 9*a + 22 ≠ 2^(246+24300*k+0+2) := by
  have h : 27*2^a + 9*a + 22 ≠ 2^((246+24300*k+0+2 - 5)+5) :=
    SheepIndependentGap.no_special_equal 27 9 22 4 5 4
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+0+2 - 5) (by omega) a
  have he : (246+24300*k+0+2 - 5)+5 = 246+24300*k+0+2 := by omega
  simpa only [he] using h
#print axioms special_246_0_2

theorem special_246_1_0 (k a : Nat) :
    243*2^a + 81*a + 311 ≠ 2^(246+24300*k+5+0) := by
  have h : 243*2^a + 81*a + 311 ≠ 2^((246+24300*k+5+0 - 8)+8) :=
    SheepIndependentGap.no_special_equal 243 81 311 7 13 6
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+5+0 - 8) (by omega) a
  have he : (246+24300*k+5+0 - 8)+8 = 246+24300*k+5+0 := by omega
  simpa only [he] using h
#print axioms special_246_1_0

theorem special_246_2_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(246+24300*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((246+24300*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+3+0 - 6) (by omega) a
  have he : (246+24300*k+3+0 - 6)+6 = 246+24300*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_246_2_0

theorem special_246_2_1 (k a : Nat) :
    135*2^a + 45*a + 124 ≠ 2^(246+24300*k+3+1) := by
  have h : 135*2^a + 45*a + 124 ≠ 2^((246+24300*k+3+1 - 8)+8) :=
    SheepIndependentGap.no_special_equal 135 45 124 7 121 1
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+3+1 - 8) (by omega) a
  have he : (246+24300*k+3+1 - 8)+8 = 246+24300*k+3+1 := by omega
  simpa only [he] using h
#print axioms special_246_2_1

theorem special_246_2_2 (k a : Nat) :
    405*2^a + 135*a + 338 ≠ 2^(246+24300*k+3+2) := by
  have h : 405*2^a + 135*a + 338 ≠ 2^((246+24300*k+3+2 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 338 8 107 3
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+3+2 - 9) (by omega) a
  have he : (246+24300*k+3+2 - 9)+9 = 246+24300*k+3+2 := by omega
  simpa only [he] using h
#print axioms special_246_2_2

theorem special_246_2_3 (k a : Nat) :
    1215*2^a + 405*a + 946 ≠ 2^(246+24300*k+3+3) := by
  have h : 1215*2^a + 405*a + 946 ≠ 2^((246+24300*k+3+3 - 11)+11) :=
    SheepIndependentGap.no_special_equal 1215 405 946 10 833 1
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+3+3 - 11) (by omega) a
  have he : (246+24300*k+3+3 - 11)+11 = 246+24300*k+3+3 := by omega
  simpa only [he] using h
#print axioms special_246_2_3

theorem special_246_3_0 (k a : Nat) :
    6075*2^a + 2025*a + 5809 ≠ 2^(246+24300*k+8+0) := by
  have h : 6075*2^a + 2025*a + 5809 ≠ 2^((246+24300*k+8+0 - 13)+13) :=
    SheepIndependentGap.no_special_equal 6075 2025 5809 12 2117 3
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+8+0 - 13) (by omega) a
  have he : (246+24300*k+8+0 - 13)+13 = 246+24300*k+8+0 := by omega
  simpa only [he] using h
#print axioms special_246_3_0

theorem special_246_4_0 (k a : Nat) :
    675*2^a + 225*a + 721 ≠ 2^(246+24300*k+6+0) := by
  have h : 675*2^a + 225*a + 721 ≠ 2^((246+24300*k+6+0 - 10)+10) :=
    SheepIndependentGap.no_special_equal 675 225 721 9 349 2
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+6+0 - 10) (by omega) a
  have he : (246+24300*k+6+0 - 10)+10 = 246+24300*k+6+0 := by omega
  simpa only [he] using h
#print axioms special_246_4_0

theorem special_246_4_1 (k a : Nat) :
    2025*2^a + 675*a + 1892 ≠ 2^(246+24300*k+6+1) := by
  have h : 2025*2^a + 675*a + 1892 ≠ 2^((246+24300*k+6+1 - 11)+11) :=
    SheepIndependentGap.no_special_equal 2025 675 1892 10 23 9
      (by decide) (by decide) (by decide) (by decide)
      (246+24300*k+6+1 - 11) (by omega) a
  have he : (246+24300*k+6+1 - 11)+11 = 246+24300*k+6+1 := by omega
  simpa only [he] using h
#print axioms special_246_4_1

theorem special_558_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(558+8100*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((558+8100*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+0+0 - 2) (by omega) a
  have he : (558+8100*k+0+0 - 2)+2 = 558+8100*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_558_0_0

theorem special_558_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(558+8100*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((558+8100*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+0+1 - 4) (by omega) a
  have he : (558+8100*k+0+1 - 4)+4 = 558+8100*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_558_0_1

theorem special_558_0_2 (k a : Nat) :
    27*2^a + 9*a + 22 ≠ 2^(558+8100*k+0+2) := by
  have h : 27*2^a + 9*a + 22 ≠ 2^((558+8100*k+0+2 - 5)+5) :=
    SheepIndependentGap.no_special_equal 27 9 22 4 5 4
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+0+2 - 5) (by omega) a
  have he : (558+8100*k+0+2 - 5)+5 = 558+8100*k+0+2 := by omega
  simpa only [he] using h
#print axioms special_558_0_2

theorem special_558_0_3 (k a : Nat) :
    81*2^a + 27*a + 62 ≠ 2^(558+8100*k+0+3) := by
  have h : 81*2^a + 27*a + 62 ≠ 2^((558+8100*k+0+3 - 7)+7) :=
    SheepIndependentGap.no_special_equal 81 27 62 6 47 1
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+0+3 - 7) (by omega) a
  have he : (558+8100*k+0+3 - 7)+7 = 558+8100*k+0+3 := by omega
  simpa only [he] using h
#print axioms special_558_0_3

theorem special_558_1_0 (k a : Nat) :
    405*2^a + 135*a + 383 ≠ 2^(558+8100*k+5+0) := by
  have h : 405*2^a + 135*a + 383 ≠ 2^((558+8100*k+5+0 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 383 8 107 3
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+5+0 - 9) (by omega) a
  have he : (558+8100*k+5+0 - 9)+9 = 558+8100*k+5+0 := by omega
  simpa only [he] using h
#print axioms special_558_1_0

theorem special_558_2_0 (k a : Nat) :
    2025*2^a + 675*a + 2207 ≠ 2^(558+8100*k+7+0) := by
  have h : 2025*2^a + 675*a + 2207 ≠ 2^((558+8100*k+7+0 - 11)+11) :=
    SheepIndependentGap.no_special_equal 2025 675 2207 10 23 9
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+7+0 - 11) (by omega) a
  have he : (558+8100*k+7+0 - 11)+11 = 558+8100*k+7+0 := by omega
  simpa only [he] using h
#print axioms special_558_2_0

theorem special_558_3_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(558+8100*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((558+8100*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+3+0 - 6) (by omega) a
  have he : (558+8100*k+3+0 - 6)+6 = 558+8100*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_558_3_0

theorem special_558_3_1 (k a : Nat) :
    135*2^a + 45*a + 124 ≠ 2^(558+8100*k+3+1) := by
  have h : 135*2^a + 45*a + 124 ≠ 2^((558+8100*k+3+1 - 8)+8) :=
    SheepIndependentGap.no_special_equal 135 45 124 7 121 1
      (by decide) (by decide) (by decide) (by decide)
      (558+8100*k+3+1 - 8) (by omega) a
  have he : (558+8100*k+3+1 - 8)+8 = 558+8100*k+3+1 := by omega
  simpa only [he] using h
#print axioms special_558_3_1

theorem special_846_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(846+8100*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((846+8100*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+0+0 - 2) (by omega) a
  have he : (846+8100*k+0+0 - 2)+2 = 846+8100*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_846_0_0

theorem special_846_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(846+8100*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((846+8100*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+0+1 - 4) (by omega) a
  have he : (846+8100*k+0+1 - 4)+4 = 846+8100*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_846_0_1

theorem special_846_0_2 (k a : Nat) :
    27*2^a + 9*a + 22 ≠ 2^(846+8100*k+0+2) := by
  have h : 27*2^a + 9*a + 22 ≠ 2^((846+8100*k+0+2 - 5)+5) :=
    SheepIndependentGap.no_special_equal 27 9 22 4 5 4
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+0+2 - 5) (by omega) a
  have he : (846+8100*k+0+2 - 5)+5 = 846+8100*k+0+2 := by omega
  simpa only [he] using h
#print axioms special_846_0_2

theorem special_846_0_3 (k a : Nat) :
    81*2^a + 27*a + 62 ≠ 2^(846+8100*k+0+3) := by
  have h : 81*2^a + 27*a + 62 ≠ 2^((846+8100*k+0+3 - 7)+7) :=
    SheepIndependentGap.no_special_equal 81 27 62 6 47 1
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+0+3 - 7) (by omega) a
  have he : (846+8100*k+0+3 - 7)+7 = 846+8100*k+0+3 := by omega
  simpa only [he] using h
#print axioms special_846_0_3

theorem special_846_1_0 (k a : Nat) :
    405*2^a + 135*a + 383 ≠ 2^(846+8100*k+5+0) := by
  have h : 405*2^a + 135*a + 383 ≠ 2^((846+8100*k+5+0 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 383 8 107 3
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+5+0 - 9) (by omega) a
  have he : (846+8100*k+5+0 - 9)+9 = 846+8100*k+5+0 := by omega
  simpa only [he] using h
#print axioms special_846_1_0

theorem special_846_2_0 (k a : Nat) :
    26325*2^a + 8775*a + 63797 ≠ 2^(846+8100*k+11+0) := by
  have h : 26325*2^a + 8775*a + 63797 ≠ 2^((846+8100*k+11+0 - 15)+15) :=
    SheepIndependentGap.no_special_equal 26325 8775 63797 14 6443 4
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+11+0 - 15) (by omega) a
  have he : (846+8100*k+11+0 - 15)+15 = 846+8100*k+11+0 := by omega
  simpa only [he] using h
#print axioms special_846_2_0

theorem special_846_3_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(846+8100*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((846+8100*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+3+0 - 6) (by omega) a
  have he : (846+8100*k+3+0 - 6)+6 = 846+8100*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_846_3_0

theorem special_846_3_1 (k a : Nat) :
    135*2^a + 45*a + 124 ≠ 2^(846+8100*k+3+1) := by
  have h : 135*2^a + 45*a + 124 ≠ 2^((846+8100*k+3+1 - 8)+8) :=
    SheepIndependentGap.no_special_equal 135 45 124 7 121 1
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+3+1 - 8) (by omega) a
  have he : (846+8100*k+3+1 - 8)+8 = 846+8100*k+3+1 := by omega
  simpa only [he] using h
#print axioms special_846_3_1

theorem special_846_4_0 (k a : Nat) :
    675*2^a + 225*a + 721 ≠ 2^(846+8100*k+6+0) := by
  have h : 675*2^a + 225*a + 721 ≠ 2^((846+8100*k+6+0 - 10)+10) :=
    SheepIndependentGap.no_special_equal 675 225 721 9 349 2
      (by decide) (by decide) (by decide) (by decide)
      (846+8100*k+6+0 - 10) (by omega) a
  have he : (846+8100*k+6+0 - 10)+10 = 846+8100*k+6+0 := by omega
  simpa only [he] using h
#print axioms special_846_4_0

theorem special_702_0_0 (k a : Nat) :
    3*2^a + 1*a + 3 ≠ 2^(702+11340*k+0+0) := by
  have h : 3*2^a + 1*a + 3 ≠ 2^((702+11340*k+0+0 - 2)+2) :=
    SheepIndependentGap.no_special_equal 3 1 3 1 1 3
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+0+0 - 2) (by omega) a
  have he : (702+11340*k+0+0 - 2)+2 = 702+11340*k+0+0 := by omega
  simpa only [he] using h
#print axioms special_702_0_0

theorem special_702_0_1 (k a : Nat) :
    9*2^a + 3*a + 8 ≠ 2^(702+11340*k+0+1) := by
  have h : 9*2^a + 3*a + 8 ≠ 2^((702+11340*k+0+1 - 4)+4) :=
    SheepIndependentGap.no_special_equal 9 3 8 3 7 1
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+0+1 - 4) (by omega) a
  have he : (702+11340*k+0+1 - 4)+4 = 702+11340*k+0+1 := by omega
  simpa only [he] using h
#print axioms special_702_0_1

theorem special_702_0_2 (k a : Nat) :
    27*2^a + 9*a + 22 ≠ 2^(702+11340*k+0+2) := by
  have h : 27*2^a + 9*a + 22 ≠ 2^((702+11340*k+0+2 - 5)+5) :=
    SheepIndependentGap.no_special_equal 27 9 22 4 5 4
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+0+2 - 5) (by omega) a
  have he : (702+11340*k+0+2 - 5)+5 = 702+11340*k+0+2 := by omega
  simpa only [he] using h
#print axioms special_702_0_2

theorem special_702_0_3 (k a : Nat) :
    81*2^a + 27*a + 62 ≠ 2^(702+11340*k+0+3) := by
  have h : 81*2^a + 27*a + 62 ≠ 2^((702+11340*k+0+3 - 7)+7) :=
    SheepIndependentGap.no_special_equal 81 27 62 6 47 1
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+0+3 - 7) (by omega) a
  have he : (702+11340*k+0+3 - 7)+7 = 702+11340*k+0+3 := by omega
  simpa only [he] using h
#print axioms special_702_0_3

theorem special_702_0_4 (k a : Nat) :
    243*2^a + 81*a + 178 ≠ 2^(702+11340*k+0+4) := by
  have h : 243*2^a + 81*a + 178 ≠ 2^((702+11340*k+0+4 - 8)+8) :=
    SheepIndependentGap.no_special_equal 243 81 178 7 13 6
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+0+4 - 8) (by omega) a
  have he : (702+11340*k+0+4 - 8)+8 = 702+11340*k+0+4 := by omega
  simpa only [he] using h
#print axioms special_702_0_4

theorem special_702_1_0 (k a : Nat) :
    405*2^a + 135*a + 383 ≠ 2^(702+11340*k+5+0) := by
  have h : 405*2^a + 135*a + 383 ≠ 2^((702+11340*k+5+0 - 9)+9) :=
    SheepIndependentGap.no_special_equal 405 135 383 8 107 3
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+5+0 - 9) (by omega) a
  have he : (702+11340*k+5+0 - 9)+9 = 702+11340*k+5+0 := by omega
  simpa only [he] using h
#print axioms special_702_1_0

theorem special_702_1_1 (k a : Nat) :
    1215*2^a + 405*a + 1036 ≠ 2^(702+11340*k+5+1) := by
  have h : 1215*2^a + 405*a + 1036 ≠ 2^((702+11340*k+5+1 - 11)+11) :=
    SheepIndependentGap.no_special_equal 1215 405 1036 10 833 1
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+5+1 - 11) (by omega) a
  have he : (702+11340*k+5+1 - 11)+11 = 702+11340*k+5+1 := by omega
  simpa only [he] using h
#print axioms special_702_1_1

theorem special_702_2_0 (k a : Nat) :
    45*2^a + 15*a + 47 ≠ 2^(702+11340*k+3+0) := by
  have h : 45*2^a + 15*a + 47 ≠ 2^((702+11340*k+3+0 - 6)+6) :=
    SheepIndependentGap.no_special_equal 45 15 47 5 19 3
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+3+0 - 6) (by omega) a
  have he : (702+11340*k+3+0 - 6)+6 = 702+11340*k+3+0 := by omega
  simpa only [he] using h
#print axioms special_702_2_0

theorem special_702_2_1 (k a : Nat) :
    135*2^a + 45*a + 124 ≠ 2^(702+11340*k+3+1) := by
  have h : 135*2^a + 45*a + 124 ≠ 2^((702+11340*k+3+1 - 8)+8) :=
    SheepIndependentGap.no_special_equal 135 45 124 7 121 1
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+3+1 - 8) (by omega) a
  have he : (702+11340*k+3+1 - 8)+8 = 702+11340*k+3+1 := by omega
  simpa only [he] using h
#print axioms special_702_2_1

theorem special_702_3_0 (k a : Nat) :
    1215*2^a + 405*a + 1667 ≠ 2^(702+11340*k+7+0) := by
  have h : 1215*2^a + 405*a + 1667 ≠ 2^((702+11340*k+7+0 - 11)+11) :=
    SheepIndependentGap.no_special_equal 1215 405 1667 10 833 2
      (by decide) (by decide) (by decide) (by decide)
      (702+11340*k+7+0 - 11) (by omega) a
  have he : (702+11340*k+7+0 - 11)+11 = 702+11340*k+7+0 := by omega
  simpa only [he] using h
#print axioms special_702_3_0

end SheepFiveSpecial
