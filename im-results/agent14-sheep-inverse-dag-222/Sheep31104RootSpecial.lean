import IndependentExceptionalGap
namespace Sheep31104RootSpecial
/-- No exceptional odd-part-three Sheep first-even parent exists for any
 j=31104+40824*k, with any hidden odd-block length. -/
theorem root_no_special (k h a : Nat) (hh : h<7)
    (hs : 3^h*(3*2^a+a+2)+2^h=2^((31104+40824*k)+h)) : False := by
  have hc : h=0 ∨ h=1 ∨ h=2 ∨ h=3 ∨ h=4 ∨ h=5 ∨ h=6 := by omega
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6
  · subst h
    have hbad := SheepIndependentGap.no_special_equal
      3 1 3 1 1 10 (by decide) (by decide) (by decide) (by decide)
      (31102+40824*k) (by omega) a
    have he : (31104+40824*k)+0=(31102+40824*k)+1+1 := by omega
    have hs' : 3*2^a+1*a+3 = 2^((31102+40824*k)+1+1) := by
      rw [←he]
      have hb3 : (3:Nat)^0=1 := by decide
      have hb2 : (2:Nat)^0=1 := by decide
      omega
    exact hbad hs'
  · subst h
    have hbad := SheepIndependentGap.no_special_equal
      9 3 8 3 7 10 (by decide) (by decide) (by decide) (by decide)
      (31101+40824*k) (by omega) a
    have he : (31104+40824*k)+1=(31101+40824*k)+3+1 := by omega
    have hs' : 9*2^a+3*a+8 = 2^((31101+40824*k)+3+1) := by
      rw [←he]
      have hb3 : (3:Nat)^1=3 := by decide
      have hb2 : (2:Nat)^1=2 := by decide
      omega
    exact hbad hs'
  · subst h
    have hbad := SheepIndependentGap.no_special_equal
      27 9 22 4 5 10 (by decide) (by decide) (by decide) (by decide)
      (31101+40824*k) (by omega) a
    have he : (31104+40824*k)+2=(31101+40824*k)+4+1 := by omega
    have hs' : 27*2^a+9*a+22 = 2^((31101+40824*k)+4+1) := by
      rw [←he]
      have hb3 : (3:Nat)^2=9 := by decide
      have hb2 : (2:Nat)^2=4 := by decide
      omega
    exact hbad hs'
  · subst h
    have hbad := SheepIndependentGap.no_special_equal
      81 27 62 6 47 10 (by decide) (by decide) (by decide) (by decide)
      (31100+40824*k) (by omega) a
    have he : (31104+40824*k)+3=(31100+40824*k)+6+1 := by omega
    have hs' : 81*2^a+27*a+62 = 2^((31100+40824*k)+6+1) := by
      rw [←he]
      have hb3 : (3:Nat)^3=27 := by decide
      have hb2 : (2:Nat)^3=8 := by decide
      omega
    exact hbad hs'
  · subst h
    have hbad := SheepIndependentGap.no_special_equal
      243 81 178 7 13 10 (by decide) (by decide) (by decide) (by decide)
      (31100+40824*k) (by omega) a
    have he : (31104+40824*k)+4=(31100+40824*k)+7+1 := by omega
    have hs' : 243*2^a+81*a+178 = 2^((31100+40824*k)+7+1) := by
      rw [←he]
      have hb3 : (3:Nat)^4=81 := by decide
      have hb2 : (2:Nat)^4=16 := by decide
      omega
    exact hbad hs'
  · subst h
    have hbad := SheepIndependentGap.no_special_equal
      729 243 518 9 295 10 (by decide) (by decide) (by decide) (by decide)
      (31099+40824*k) (by omega) a
    have he : (31104+40824*k)+5=(31099+40824*k)+9+1 := by omega
    have hs' : 729*2^a+243*a+518 = 2^((31099+40824*k)+9+1) := by
      rw [←he]
      have hb3 : (3:Nat)^5=243 := by decide
      have hb2 : (2:Nat)^5=32 := by decide
      omega
    exact hbad hs'
  · subst h
    have hbad := SheepIndependentGap.no_special_equal
      2187 729 1522 11 1909 10 (by decide) (by decide) (by decide) (by decide)
      (31098+40824*k) (by omega) a
    have he : (31104+40824*k)+6=(31098+40824*k)+11+1 := by omega
    have hs' : 2187*2^a+729*a+1522 = 2^((31098+40824*k)+11+1) := by
      rw [←he]
      have hb3 : (3:Nat)^6=729 := by decide
      have hb2 : (2:Nat)^6=64 := by decide
      omega
    exact hbad hs'
#print axioms root_no_special
end Sheep31104RootSpecial
