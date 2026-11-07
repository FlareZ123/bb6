import Sheep31104RootBound
import Sheep31104RootHigh
import Sheep31104RootSpecial
import SheepEdgeIdentities
import Sheep31104RootLow0
import Sheep31104RootLow1
import Sheep31104RootLow2
import Sheep31104RootLow3
import Sheep31104RootLow4
import Sheep31104RootLow5
import Sheep31104RootLow6

namespace Sheep31104RootComplete

/-- Every original even E predecessor of the target power must be the
single rational-affine Z node. Fully quantified over k, h, and a. -/
theorem root_parent_is_Z (k x : Nat)
  (hCases :
    (∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ 2^(31104+122472*k)=1+3^h*u ∧
      (1*3^h)*(2^(a+1)+1)*v + 2*a*(1*3^h) +
        2^(h+1)*1 + 2^(h+1)*0 =
          2^((31104+122472*k)+h+1) + 3*(1*3^h)) ∨
    (∃ a h u : Nat,
      1 ≤ a ∧ u%2=1 ∧ x=3*2^a ∧
      2^(31104+122472*k)=1+3^h*u ∧
      (1*3^h)*(3*2^a+a+2)+2^h*1+2^h*0 =
        2^((31104+122472*k)+h))) :
  3483*x+16576=2^(31114+122472*k) := by
  rcases hCases with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hy,hs⟩ |
    ⟨a,h,u,ha,hu,hx,hy,hs⟩
  · have hh : h<7 :=
      Sheep31104RootBound.root_h_lt_seven k h u hy
    have hs0 : 3^h*(2^(a+1)+1)*v+2*a*3^h+2^(h+1)=
        2^((31104+122472*k)+h+1)+3*3^h := by
      simpa only [Nat.one_mul, Nat.mul_one, Nat.mul_zero, Nat.add_zero] using hs
    by_cases hhigh : 15≤a
    · exact False.elim (Sheep31104RootHigh.no_high k a h v hhigh hh hs0)
    · have hlo : 1≤a ∧ a<15 := by omega
      have hc : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 := by omega
      rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6
      · subst h
        have haCases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by omega
        rcases haCases with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 | a12 | a13 | a14
        · subst a
          exact False.elim (Sheep31104RootLow0.a1_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a2_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a3_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a4_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a5_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a6_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a7_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a8_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a9_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a10_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a11_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a12_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a13_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow0.a14_source k v hs0)
      · subst h
        have haCases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by omega
        rcases haCases with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 | a12 | a13 | a14
        · subst a
          exact False.elim (Sheep31104RootLow1.a1_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a2_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a3_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a4_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a5_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a6_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a7_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a8_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a9_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a10_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a11_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a12_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a13_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow1.a14_source k v hs0)
      · subst h
        have haCases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by omega
        rcases haCases with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 | a12 | a13 | a14
        · subst a
          exact False.elim (Sheep31104RootLow2.a1_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a2_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a3_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a4_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a5_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a6_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a7_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a8_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a9_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a10_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a11_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a12_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a13_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow2.a14_source k v hs0)
      · subst h
        have haCases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by omega
        rcases haCases with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 | a12 | a13 | a14
        · subst a
          exact False.elim (Sheep31104RootLow3.a1_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a2_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a3_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a4_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a5_source k v hs0)
        · subst a
          have hraw : (1*3^3)*(2^(6+1)+1)*v + 2*6*(1*3^3) + 2^(3+1)*1+2^(3+1)*0 =
              2^((31104+122472*k)+3+1)+3*(1*3^3) := by
            simpa only [Nat.one_mul, Nat.mul_one, Nat.mul_zero, Nat.add_zero] using hs0
          have hZ : 3483*x+16576=2^((31104+122472*k)+10) :=
            SheepEdgeIdentities.root_h3_a6_to_Z (31104+122472*k) x v hx hraw
          simpa only [show (31104+122472*k)+10=31114+122472*k by omega] using hZ
        · subst a
          exact False.elim (Sheep31104RootLow3.a7_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a8_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a9_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a10_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a11_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a12_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a13_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow3.a14_source k v hs0)
      · subst h
        have haCases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by omega
        rcases haCases with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 | a12 | a13 | a14
        · subst a
          exact False.elim (Sheep31104RootLow4.a1_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a2_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a3_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a4_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a5_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a6_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a7_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a8_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a9_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a10_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a11_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a12_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a13_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow4.a14_source k v hs0)
      · subst h
        have haCases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by omega
        rcases haCases with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 | a12 | a13 | a14
        · subst a
          exact False.elim (Sheep31104RootLow5.a1_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a2_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a3_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a4_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a5_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a6_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a7_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a8_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a9_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a10_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a11_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a12_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a13_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow5.a14_source k v hs0)
      · subst h
        have haCases : a=1 ∨ a=2 ∨ a=3 ∨ a=4 ∨ a=5 ∨ a=6 ∨ a=7 ∨ a=8 ∨ a=9 ∨ a=10 ∨ a=11 ∨ a=12 ∨ a=13 ∨ a=14 := by omega
        rcases haCases with a1 | a2 | a3 | a4 | a5 | a6 | a7 | a8 | a9 | a10 | a11 | a12 | a13 | a14
        · subst a
          exact False.elim (Sheep31104RootLow6.a1_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a2_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a3_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a4_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a5_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a6_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a7_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a8_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a9_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a10_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a11_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a12_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a13_source k v hs0)
        · subst a
          exact False.elim (Sheep31104RootLow6.a14_source k v hs0)
  · have hh : h<7 :=
      Sheep31104RootBound.root_h_lt_seven k h u hy
    have hs0 : 3^h*(3*2^a+a+2)+2^h=2^((31104+122472*k)+h) := by
      simpa only [Nat.one_mul, Nat.mul_one, Nat.mul_zero, Nat.add_zero] using hs
    exact False.elim (Sheep31104RootSpecial.root_no_special k h a hh hs0)

#print axioms root_parent_is_Z
end Sheep31104RootComplete
