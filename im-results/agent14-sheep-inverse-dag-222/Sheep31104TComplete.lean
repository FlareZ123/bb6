import Sheep31104TBound
import Sheep31104THigh
import Sheep31104TLow
import Sheep31104TSpecial
namespace Sheep31104TComplete

/-- Every exact original-source generic or exceptional inverse equation into T
is impossible for every k. No finite simulation horizon is imposed. -/
theorem T_no_source (k x y : Nat)
  (hTarget : 31347*y+174404=2^(31117+40824*k))
  (hCases :
    (∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (31347*3^h)*(2^(a+1)+1)*v + 2*a*(31347*3^h) +
        2^(h+1)*31347 + 2^(h+1)*174404 =
          2^((31117+40824*k)+h+1) + 3*(31347*3^h)) ∨
    (∃ a h u : Nat,
      1 ≤ a ∧ u%2=1 ∧ x=3*2^a ∧ y=1+3^h*u ∧
      (31347*3^h)*(3*2^a+a+2)+2^h*31347+2^h*174404 =
        2^((31117+40824*k)+h))) : False := by
  rcases hCases with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hy,hs⟩ |
    ⟨a,h,u,ha,hu,hx,hy,hs⟩
  · have hh : h=0 :=
      Sheep31104TBound.T_hidden_h_zero k y h u hTarget hy
    subst h
    have he : (31117+40824*k)+0+1=31118+40824*k := by omega
    have hs0 :
      31347*(2^(a+1)+1)*v + 2*a*31347 + 2*31347 + 2*174404 =
      2^(31118+40824*k)+3*31347 := by
      simpa only [show (3:Nat)^0=1 by decide, Nat.mul_one,
        show (2:Nat)^(0+1)=2 by decide,he] using hs
    have hnotHigh : a<21 := by
      by_cases hb : a<21
      · exact hb
      · have hhigh : 21≤a := by omega
        exact False.elim (Sheep31104THigh.T_generic_high k a v hhigh hs0)
    have hnot1 : a≠1 := by
      intro h
      subst a
      exact Sheep31104TLow.a1_source k v hs0
    have hnot2 : a≠2 := by
      intro h
      subst a
      exact Sheep31104TLow.a2_source k v hs0
    have hnot3 : a≠3 := by
      intro h
      subst a
      exact Sheep31104TLow.a3_source k v hs0
    have hnot4 : a≠4 := by
      intro h
      subst a
      exact Sheep31104TLow.a4_source k v hs0
    have hnot5 : a≠5 := by
      intro h
      subst a
      exact Sheep31104TLow.a5_source k v hs0
    have hnot6 : a≠6 := by
      intro h
      subst a
      exact Sheep31104TLow.a6_source k v hs0
    have hnot7 : a≠7 := by
      intro h
      subst a
      exact Sheep31104TLow.a7_source k v hs0
    have hnot8 : a≠8 := by
      intro h
      subst a
      exact Sheep31104TLow.a8_source k v hs0
    have hnot9 : a≠9 := by
      intro h
      subst a
      exact Sheep31104TLow.a9_source k v hs0
    have hnot10 : a≠10 := by
      intro h
      subst a
      exact Sheep31104TLow.a10_source k v hs0
    have hnot11 : a≠11 := by
      intro h
      subst a
      exact Sheep31104TLow.a11_source k v hs0
    have hnot12 : a≠12 := by
      intro h
      subst a
      exact Sheep31104TLow.a12_source k v hs0
    have hnot13 : a≠13 := by
      intro h
      subst a
      exact Sheep31104TLow.a13_source k v hs0
    have hnot14 : a≠14 := by
      intro h
      subst a
      exact Sheep31104TLow.a14_source k v hs0
    have hnot15 : a≠15 := by
      intro h
      subst a
      exact Sheep31104TLow.a15_source k v hs0
    have hnot16 : a≠16 := by
      intro h
      subst a
      exact Sheep31104TLow.a16_source k v hs0
    have hnot17 : a≠17 := by
      intro h
      subst a
      exact Sheep31104TLow.a17_source k v hs0
    have hnot18 : a≠18 := by
      intro h
      subst a
      exact Sheep31104TLow.a18_source k v hs0
    have hnot19 : a≠19 := by
      intro h
      subst a
      exact Sheep31104TLow.a19_source k v hs0
    have hnot20 : a≠20 := by
      intro h
      subst a
      exact Sheep31104TLow.a20_source k v hs0
    omega
  · have hh : h=0 :=
      Sheep31104TBound.T_hidden_h_zero k y h u hTarget hy
    subst h
    have hepower : (31117+40824*k)+0=31117+40824*k := by omega
    have hs0 :
      31347*(3*2^a+a+2)+2^0*31347+2^0*174404 =
      2^(31117+40824*k) := by
      simpa only [show (3:Nat)^0=1 by decide,Nat.mul_one,hepower] using hs
    exact Sheep31104TSpecial.T_no_exceptional k a hs0

#print axioms T_no_source
end Sheep31104TComplete
