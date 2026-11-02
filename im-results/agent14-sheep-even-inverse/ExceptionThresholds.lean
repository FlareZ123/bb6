import ExceptionalBound
namespace SheepEvenBound

/-- At every n>=6, all three exponential gap conditions hold for node 0 h=0. -/
theorem exceptional_0_0 (n : Nat) (hn : 6 ≤ n) :
    1*2^(n-2)>1*(n+3)+0 ∧ 2^(n-2)>2*1 := by
  have hne : 4 ≤ n-2 := by omega
  have hg := growth 1 1 2 4 (n-2) (by decide) (by decide) (by decide) hne
  have hlin : 1*((n-2)+3)+2=1*(n+3)+0 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=7, all three exponential gap conditions hold for node 0 h=1. -/
theorem exceptional_0_1 (n : Nat) (hn : 7 ≤ n) :
    7*2^(n-4)>3*(n+3)+1 ∧ 2^(n-4)>2*3 := by
  have hne : 3 ≤ n-4 := by omega
  have hg := growth 3 7 13 3 (n-4) (by decide) (by decide) (by decide) hne
  have hlin : 3*((n-4)+3)+13=3*(n+3)+1 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=10, all three exponential gap conditions hold for node 0 h=2. -/
theorem exceptional_0_2 (n : Nat) (hn : 10 ≤ n) :
    5*2^(n-5)>9*(n+3)+5 ∧ 2^(n-5)>2*9 := by
  have hne : 5 ≤ n-5 := by omega
  have hg := growth 9 5 50 5 (n-5) (by decide) (by decide) (by decide) hne
  have hlin : 9*((n-5)+3)+50=9*(n+3)+5 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=11, all three exponential gap conditions hold for node 1 h=0. -/
theorem exceptional_1_0 (n : Nat) (hn : 11 ≤ n) :
    19*2^(n-6)>15*(n+3)+2 ∧ 2^(n-6)>2*15 := by
  have hne : 5 ≤ n-6 := by omega
  have hg := growth 15 19 92 5 (n-6) (by decide) (by decide) (by decide) hne
  have hlin : 15*((n-6)+3)+92=15*(n+3)+2 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=15, all three exponential gap conditions hold for node 1 h=1. -/
theorem exceptional_1_1 (n : Nat) (hn : 15 ≤ n) :
    121*2^(n-8)>45*(n+3)+11 ∧ 2^(n-8)>2*45 := by
  have hne : 7 ≤ n-8 := by omega
  have hg := growth 45 121 371 7 (n-8) (by decide) (by decide) (by decide) hne
  have hlin : 45*((n-8)+3)+371=45*(n+3)+11 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=18, all three exponential gap conditions hold for node 1 h=2. -/
theorem exceptional_1_2 (n : Nat) (hn : 18 ≤ n) :
    107*2^(n-9)>135*(n+3)+67 ∧ 2^(n-9)>2*135 := by
  have hne : 9 ≤ n-9 := by omega
  have hg := growth 135 107 1282 9 (n-9) (by decide) (by decide) (by decide) hne
  have hlin : 135*((n-9)+3)+1282=135*(n+3)+67 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=21, all three exponential gap conditions hold for node 1 h=3. -/
theorem exceptional_1_3 (n : Nat) (hn : 21 ≤ n) :
    833*2^(n-11)>405*(n+3)+269 ∧ 2^(n-11)>2*405 := by
  have hne : 10 ≤ n-11 := by omega
  have hg := growth 405 833 4724 10 (n-11) (by decide) (by decide) (by decide) hne
  have hlin : 405*((n-11)+3)+4724=405*(n+3)+269 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=16, all three exponential gap conditions hold for node 2 h=0. -/
theorem exceptional_2_0 (n : Nat) (hn : 16 ≤ n) :
    13*2^(n-8)>81*(n+3)+68 ∧ 2^(n-8)>2*81 := by
  have hne : 8 ≤ n-8 := by omega
  have hg := growth 81 13 716 8 (n-8) (by decide) (by decide) (by decide) hne
  have hlin : 81*((n-8)+3)+716=81*(n+3)+68 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

/-- At every n>=19, all three exponential gap conditions hold for node 2 h=1. -/
theorem exceptional_2_1 (n : Nat) (hn : 19 ≤ n) :
    295*2^(n-10)>243*(n+3)+55 ∧ 2^(n-10)>2*243 := by
  have hne : 9 ≤ n-10 := by omega
  have hg := growth 243 295 2485 9 (n-10) (by decide) (by decide) (by decide) hne
  have hlin : 243*((n-10)+3)+2485=243*(n+3)+55 := by omega
  constructor
  · rw [←hlin]; exact hg.1
  · exact hg.2

#print axioms exceptional_0_0
#print axioms exceptional_0_1
#print axioms exceptional_0_2
#print axioms exceptional_1_0
#print axioms exceptional_1_1
#print axioms exceptional_1_2
#print axioms exceptional_1_3
#print axioms exceptional_2_0
#print axioms exceptional_2_1
end SheepEvenBound
