import SheepGenericHigh
namespace SheepHighCases

theorem high_r402_n0_h0 (a : Nat) (ha : 2≤a) :
  1<SheepGenericHigh.Q 1 2 a ∧
  SheepGenericHigh.Q 1 2 a % 2 = 1 ∧
  SheepGenericHigh.Q 1 2 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 1 2 2 (by decide) (by decide) a ha

theorem high_r402_n0_h1 (a : Nat) (ha : 5≤a) :
  1<SheepGenericHigh.Q 3 4 a ∧
  SheepGenericHigh.Q 3 4 a % 2 = 1 ∧
  SheepGenericHigh.Q 3 4 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 3 4 5 (by decide) (by decide) a ha

theorem high_r402_n0_h2 (a : Nat) (ha : 7≤a) :
  1<SheepGenericHigh.Q 9 8 a ∧
  SheepGenericHigh.Q 9 8 a % 2 = 1 ∧
  SheepGenericHigh.Q 9 8 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 9 8 7 (by decide) (by decide) a ha

theorem high_r402_n1_h0 (a : Nat) (ha : 8≤a) :
  1<SheepGenericHigh.Q 15 34 a ∧
  SheepGenericHigh.Q 15 34 a % 2 = 1 ∧
  SheepGenericHigh.Q 15 34 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 15 34 8 (by decide) (by decide) a ha

theorem high_r402_n1_h1 (a : Nat) (ha : 10≤a) :
  1<SheepGenericHigh.Q 45 68 a ∧
  SheepGenericHigh.Q 45 68 a % 2 = 1 ∧
  SheepGenericHigh.Q 45 68 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 45 68 10 (by decide) (by decide) a ha

theorem high_r402_n2_h0 (a : Nat) (ha : 16≤a) :
  1<SheepGenericHigh.Q 1485 12346 a ∧
  SheepGenericHigh.Q 1485 12346 a % 2 = 1 ∧
  SheepGenericHigh.Q 1485 12346 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 1485 12346 16 (by decide) (by decide) a ha

theorem high_r402_n2_h1 (a : Nat) (ha : 18≤a) :
  1<SheepGenericHigh.Q 4455 24692 a ∧
  SheepGenericHigh.Q 4455 24692 a % 2 = 1 ∧
  SheepGenericHigh.Q 4455 24692 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 4455 24692 18 (by decide) (by decide) a ha

theorem high_r1738_n0_h0 (a : Nat) (ha : 2≤a) :
  1<SheepGenericHigh.Q 1 2 a ∧
  SheepGenericHigh.Q 1 2 a % 2 = 1 ∧
  SheepGenericHigh.Q 1 2 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 1 2 2 (by decide) (by decide) a ha

theorem high_r1738_n0_h1 (a : Nat) (ha : 5≤a) :
  1<SheepGenericHigh.Q 3 4 a ∧
  SheepGenericHigh.Q 3 4 a % 2 = 1 ∧
  SheepGenericHigh.Q 3 4 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 3 4 5 (by decide) (by decide) a ha

theorem high_r1738_n1_h0 (a : Nat) (ha : 8≤a) :
  1<SheepGenericHigh.Q 15 34 a ∧
  SheepGenericHigh.Q 15 34 a % 2 = 1 ∧
  SheepGenericHigh.Q 15 34 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 15 34 8 (by decide) (by decide) a ha

theorem high_r1738_n2_h0 (a : Nat) (ha : 12≤a) :
  1<SheepGenericHigh.Q 135 662 a ∧
  SheepGenericHigh.Q 135 662 a % 2 = 1 ∧
  SheepGenericHigh.Q 135 662 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 135 662 12 (by decide) (by decide) a ha

theorem high_r1738_n2_h1 (a : Nat) (ha : 14≤a) :
  1<SheepGenericHigh.Q 405 1324 a ∧
  SheepGenericHigh.Q 405 1324 a % 2 = 1 ∧
  SheepGenericHigh.Q 405 1324 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 405 1324 14 (by decide) (by decide) a ha

theorem high_r1738_n2_h2 (a : Nat) (ha : 16≤a) :
  1<SheepGenericHigh.Q 1215 2648 a ∧
  SheepGenericHigh.Q 1215 2648 a % 2 = 1 ∧
  SheepGenericHigh.Q 1215 2648 a < 2^a := by
  exact SheepGenericHigh.large_odd_gap 1215 2648 16 (by decide) (by decide) a ha

#print axioms high_r402_n2_h1
#print axioms high_r1738_n2_h2
end SheepHighCases
