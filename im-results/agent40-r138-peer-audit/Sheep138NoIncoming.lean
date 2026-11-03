import Sheep138ChildLowCases
import Sheep138ChildGenericHigh
import Sheep138ChildExceptional
import Sheep138ChildHighH
import SheepEvenSourceAlgebra

namespace Sheep138NoIncoming

/-- Under original Sheep even-return semantics, every member of the
15*y+2=2^(141+4860*k) family has no incoming EvenEdge from ANY even x.
The source need not be blank-reachable. -/
theorem child1_no_incoming (k x y : Nat)
    (heven : x % 2 = 0)
    (hedge : SheepEven.EvenEdge x y)
    (ht : 15*y+2=2^(141+4860*k)) : False := by
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra heven hedge with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hz,hy⟩ |
    ⟨a,h,u,ha,hu,hx,hz,hy⟩
  · have hlt : h < 4 :=
      Sheep138ChildHighH.child1_h_lt_four k y h u ht hy
    have htarget : 15*(1+3^h*u)+2=2^(141+4860*k) := by
      rw [←hy]
      exact ht
    have hcases : h=0 ∨ h=1 ∨ h=2 ∨ h=3 := by omega
    rcases hcases with hh0 | hh1 | hh2 | hh3
    · subst h
      by_cases hlow : a < 8
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4 | ha5 | ha6 | ha7
        · subst a
          exact Sheep138ChildLowCases.no_child1_0_1 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_0_2 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_0_3 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_0_4 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_0_5 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_0_6 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_0_7 k v u hvodd htarget hz
      · exact Sheep138ChildGenericHigh.child1_h0_high
          (141+4860*k) a v u (by omega) htarget hz
    · subst h
      by_cases hlow : a < 10
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4 | ha5 | ha6 | ha7 | ha8 | ha9
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_1 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_2 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_3 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_4 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_5 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_6 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_7 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_8 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_1_9 k v u hvodd htarget hz
      · exact Sheep138ChildGenericHigh.child1_h1_high
          (141+4860*k) a v u (by omega) htarget hz
    · subst h
      by_cases hlow : a < 12
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4 | ha5 | ha6 | ha7 | ha8 | ha9 | ha10 | ha11
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_1 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_2 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_3 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_4 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_5 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_6 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_7 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_8 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_9 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_10 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_2_11 k v u hvodd htarget hz
      · exact Sheep138ChildGenericHigh.child1_h2_high
          (141+4860*k) a v u (by omega) htarget hz
    · subst h
      by_cases hlow : a < 14
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4 | ha5 | ha6 | ha7 | ha8 | ha9 | ha10 | ha11 | ha12 | ha13
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_1 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_2 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_3 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_4 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_5 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_6 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_7 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_8 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_9 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_10 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_11 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_12 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child1_3_13 k v u hvodd htarget hz
      · exact Sheep138ChildGenericHigh.child1_h3_high
          (141+4860*k) a v u (by omega) htarget hz
  · exact Sheep138ChildExceptional.child1_no_special k y a h u ht hy hz

#print axioms child1_no_incoming

/-- Under original Sheep even-return semantics, every member of the
81*y+68=2^(143+4860*k) family has no incoming EvenEdge from ANY even x.
The source need not be blank-reachable. -/
theorem child2_no_incoming (k x y : Nat)
    (heven : x % 2 = 0)
    (hedge : SheepEven.EvenEdge x y)
    (ht : 81*y+68=2^(143+4860*k)) : False := by
  rcases SheepEvenSourceAlgebra.even_edge_to_algebra heven hedge with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hz,hy⟩ |
    ⟨a,h,u,ha,hu,hx,hz,hy⟩
  · have hlt : h < 2 :=
      Sheep138ChildHighH.child2_h_lt_two k y h u ht hy
    have htarget : 81*(1+3^h*u)+68=2^(143+4860*k) := by
      rw [←hy]
      exact ht
    have hcases : h=0 ∨ h=1 := by omega
    rcases hcases with hh0 | hh1
    · subst h
      by_cases hlow : a < 11
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4 | ha5 | ha6 | ha7 | ha8 | ha9 | ha10
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_1 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_2 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_3 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_4 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_5 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_6 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_7 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_8 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_9 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_0_10 k v u hvodd htarget hz
      · exact Sheep138ChildGenericHigh.child2_h0_high
          (143+4860*k) a v u (by omega) htarget hz
    · subst h
      by_cases hlow : a < 13
      · have acases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 := by omega
        rcases acases with ha1 | ha2 | ha3 | ha4 | ha5 | ha6 | ha7 | ha8 | ha9 | ha10 | ha11 | ha12
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_1 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_2 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_3 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_4 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_5 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_6 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_7 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_8 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_9 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_10 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_11 k v u hvodd htarget hz
        · subst a
          exact Sheep138ChildLowCases.no_child2_1_12 k v u hvodd htarget hz
      · exact Sheep138ChildGenericHigh.child2_h1_high
          (143+4860*k) a v u (by omega) htarget hz
  · exact Sheep138ChildExceptional.child2_no_special k y a h u ht hy hz

#print axioms child2_no_incoming

end Sheep138NoIncoming
