import Sheep31104ZBound
import Sheep31104ZHigh
import Sheep31104ZLow
import Sheep31104ZSpecial
import SheepEdgeIdentities
namespace Sheep31104ZComplete

/-- Every genuine source inverse alternative into this affine Z target has
the same parent T. Uniform over all k and all source valuations. -/
theorem Z_parent_is_T (k x y : Nat)
  (hTarget : 3483*y+16576=2^(31114+122472*k))
  (hCases :
    (∃ a h v u : Nat,
      1 ≤ a ∧ 5 ≤ v ∧ v%2=1 ∧ u%2=1 ∧
      x=2^a*v ∧ y=1+3^h*u ∧
      (3483*3^h)*(2^(a+1)+1)*v + 2*a*(3483*3^h) +
        2^(h+1)*3483 + 2^(h+1)*16576 =
          2^((31114+122472*k)+h+1) + 3*(3483*3^h)) ∨
    (∃ a h u : Nat,
      1 ≤ a ∧ u%2=1 ∧ x=3*2^a ∧ y=1+3^h*u ∧
      (3483*3^h)*(3*2^a+a+2)+2^h*3483+2^h*16576 =
        2^((31114+122472*k)+h))) :
  31347*x+174404=2^(31117+122472*k) := by
  rcases hCases with
    ⟨a,h,v,u,ha,hv,hvodd,hu,hx,hy,hs⟩ |
    ⟨a,h,u,ha,hu,hx,hy,hs⟩
  · have hh : h=0 :=
      Sheep31104ZBound.Z_hidden_h_zero k y h u hTarget hy
    subst h
    have he : (31114+122472*k)+0+1=31115+122472*k := by omega
    have hs0 :
      3483*(2^(a+1)+1)*v + 2*a*3483 + 2*3483 + 2*16576 =
      2^(31115+122472*k)+3*3483 := by
      simpa only [show (3:Nat)^0=1 by decide, Nat.mul_one,
        show (2:Nat)^(0+1)=2 by decide,he] using hs
    have hnotHigh : a<18 := by
      by_cases hb : a<18
      · exact hb
      · have hhigh : 18≤a := by omega
        exact False.elim (Sheep31104ZHigh.Z_generic_high k a v hhigh hs0)
    have hnot1 : a≠1 := by
      intro h
      subst a
      exact Sheep31104ZLow.a1_source k v hs0
    have hnot3 : a≠3 := by
      intro h
      subst a
      exact Sheep31104ZLow.a3_source k v hs0
    have hnot4 : a≠4 := by
      intro h
      subst a
      exact Sheep31104ZLow.a4_source k v hs0
    have hnot5 : a≠5 := by
      intro h
      subst a
      exact Sheep31104ZLow.a5_source k v hs0
    have hnot6 : a≠6 := by
      intro h
      subst a
      exact Sheep31104ZLow.a6_source k v hs0
    have hnot7 : a≠7 := by
      intro h
      subst a
      exact Sheep31104ZLow.a7_source k v hs0
    have hnot8 : a≠8 := by
      intro h
      subst a
      exact Sheep31104ZLow.a8_source k v hs0
    have hnot9 : a≠9 := by
      intro h
      subst a
      exact Sheep31104ZLow.a9_source k v hs0
    have hnot10 : a≠10 := by
      intro h
      subst a
      exact Sheep31104ZLow.a10_source k v hs0
    have hnot11 : a≠11 := by
      intro h
      subst a
      exact Sheep31104ZLow.a11_source k v hs0
    have hnot12 : a≠12 := by
      intro h
      subst a
      exact Sheep31104ZLow.a12_source k v hs0
    have hnot13 : a≠13 := by
      intro h
      subst a
      exact Sheep31104ZLow.a13_source k v hs0
    have hnot14 : a≠14 := by
      intro h
      subst a
      exact Sheep31104ZLow.a14_source k v hs0
    have hnot15 : a≠15 := by
      intro h
      subst a
      exact Sheep31104ZLow.a15_source k v hs0
    have hnot16 : a≠16 := by
      intro h
      subst a
      exact Sheep31104ZLow.a16_source k v hs0
    have hnot17 : a≠17 := by
      intro h
      subst a
      exact Sheep31104ZLow.a17_source k v hs0
    have ha2 : a=2 := by omega
    subst a
    have hepower : (31104+122472*k)+10 = 31114+122472*k := by omega
    have hp : (31104+122472*k)+13 = 31117+122472*k := by omega
    have hsForEdge :
        (3483*3^0)*(2^(2+1)+1)*v + 2*2*(3483*3^0) +
        2^(0+1)*3483 + 2^(0+1)*16576 =
        2^(((31104+122472*k)+10)+0+1)+3*(3483*3^0) := by
      simpa only [show (3:Nat)^0=1 by decide, Nat.mul_one,
        show (2:Nat)^(0+1)=2 by decide,
        hepower, show (31114+122472*k)+0+1=31115+122472*k by omega]
        using hs0
    have hparent := SheepEdgeIdentities.Z_h0_a2_to_T
      (31104+122472*k) x v hx hsForEdge
    rw [hp] at hparent
    exact hparent
  · have hh : h=0 :=
      Sheep31104ZBound.Z_hidden_h_zero k y h u hTarget hy
    subst h
    have hepower : (31114+122472*k)+0=31114+122472*k := by omega
    have hs0 :
      3483*(3*2^a+a+2)+2^0*3483+2^0*16576 =
      2^(31114+122472*k) := by
      simpa only [show (3:Nat)^0=1 by decide,Nat.mul_one,hepower] using hs
    exact False.elim (Sheep31104ZSpecial.Z_no_exceptional k a hs0)
#print axioms Z_parent_is_T
end Sheep31104ZComplete
