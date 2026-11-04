import IndependentExceptionalGap
namespace SheepSpecialCases

theorem special_r402_n0_h0 (k a : Nat) :
  3*2^a + 1*a + 3 ≠ 2^(402+4860*k) := by
  have ht : 3 ≤ (402+4860*k)-1-1 := by omega
  have hs : ((402+4860*k)-1-1)+1+1 = 402+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 3 1 3 1 1 3
    (by decide) (by decide) (by decide) (by decide)
    (402+4860*k-1-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r402_n0_h1 (k a : Nat) :
  9*2^a + 3*a + 8 ≠ 2^(403+4860*k) := by
  have ht : 1 ≤ (403+4860*k)-3-1 := by omega
  have hs : ((403+4860*k)-3-1)+3+1 = 403+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 9 3 8 3 7 1
    (by decide) (by decide) (by decide) (by decide)
    (403+4860*k-3-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r402_n0_h2 (k a : Nat) :
  27*2^a + 9*a + 22 ≠ 2^(404+4860*k) := by
  have ht : 4 ≤ (404+4860*k)-4-1 := by omega
  have hs : ((404+4860*k)-4-1)+4+1 = 404+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 27 9 22 4 5 4
    (by decide) (by decide) (by decide) (by decide)
    (404+4860*k-4-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r402_n1_h0 (k a : Nat) :
  45*2^a + 15*a + 47 ≠ 2^(405+4860*k) := by
  have ht : 3 ≤ (405+4860*k)-5-1 := by omega
  have hs : ((405+4860*k)-5-1)+5+1 = 405+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 45 15 47 5 19 3
    (by decide) (by decide) (by decide) (by decide)
    (405+4860*k-5-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r402_n1_h1 (k a : Nat) :
  135*2^a + 45*a + 124 ≠ 2^(406+4860*k) := by
  have ht : 1 ≤ (406+4860*k)-7-1 := by omega
  have hs : ((406+4860*k)-7-1)+7+1 = 406+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 135 45 124 7 121 1
    (by decide) (by decide) (by decide) (by decide)
    (406+4860*k-7-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r402_n2_h0 (k a : Nat) :
  4455*2^a + 1485*a + 9143 ≠ 2^(411+4860*k) := by
  have ht : 2 ≤ (411+4860*k)-12-1 := by omega
  have hs : ((411+4860*k)-12-1)+12+1 = 411+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 4455 1485 9143 12 3737 2
    (by decide) (by decide) (by decide) (by decide)
    (411+4860*k-12-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r402_n2_h1 (k a : Nat) :
  13365*2^a + 4455*a + 21256 ≠ 2^(412+4860*k) := by
  have ht : 4 ≤ (412+4860*k)-13-1 := by omega
  have hs : ((412+4860*k)-13-1)+13+1 = 412+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 13365 4455 21256 13 3019 4
    (by decide) (by decide) (by decide) (by decide)
    (412+4860*k-13-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r1738_n0_h0 (k a : Nat) :
  3*2^a + 1*a + 3 ≠ 2^(1738+4860*k) := by
  have ht : 3 ≤ (1738+4860*k)-1-1 := by omega
  have hs : ((1738+4860*k)-1-1)+1+1 = 1738+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 3 1 3 1 1 3
    (by decide) (by decide) (by decide) (by decide)
    (1738+4860*k-1-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r1738_n0_h1 (k a : Nat) :
  9*2^a + 3*a + 8 ≠ 2^(1739+4860*k) := by
  have ht : 1 ≤ (1739+4860*k)-3-1 := by omega
  have hs : ((1739+4860*k)-3-1)+3+1 = 1739+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 9 3 8 3 7 1
    (by decide) (by decide) (by decide) (by decide)
    (1739+4860*k-3-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r1738_n1_h0 (k a : Nat) :
  45*2^a + 15*a + 47 ≠ 2^(1741+4860*k) := by
  have ht : 3 ≤ (1741+4860*k)-5-1 := by omega
  have hs : ((1741+4860*k)-5-1)+5+1 = 1741+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 45 15 47 5 19 3
    (by decide) (by decide) (by decide) (by decide)
    (1741+4860*k-5-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r1738_n2_h0 (k a : Nat) :
  405*2^a + 135*a + 601 ≠ 2^(1744+4860*k) := by
  have ht : 4 ≤ (1744+4860*k)-8-1 := by omega
  have hs : ((1744+4860*k)-8-1)+8+1 = 1744+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 405 135 601 8 107 4
    (by decide) (by decide) (by decide) (by decide)
    (1744+4860*k-8-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r1738_n2_h1 (k a : Nat) :
  1215*2^a + 405*a + 1472 ≠ 2^(1745+4860*k) := by
  have ht : 2 ≤ (1745+4860*k)-10-1 := by omega
  have hs : ((1745+4860*k)-10-1)+10+1 = 1745+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 1215 405 1472 10 833 2
    (by decide) (by decide) (by decide) (by decide)
    (1745+4860*k-10-1) ht a
  apply hgap
  simpa only [hs] using heq

theorem special_r1738_n2_h2 (k a : Nat) :
  3645*2^a + 1215*a + 3754 ≠ 2^(1746+4860*k) := by
  have ht : 5 ≤ (1746+4860*k)-11-1 := by omega
  have hs : ((1746+4860*k)-11-1)+11+1 = 1746+4860*k := by omega
  intro heq
  have hgap := SheepIndependentGap.no_special_equal 3645 1215 3754 11 451 5
    (by decide) (by decide) (by decide) (by decide)
    (1746+4860*k-11-1) ht a
  apply hgap
  simpa only [hs] using heq

#print axioms special_r402_n2_h1
#print axioms special_r1738_n2_h2
end SheepSpecialCases
