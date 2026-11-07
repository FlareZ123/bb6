import IndependentExceptionalGap
namespace Sheep31104ZSpecial

/-- The exceptional odd-part-three return cannot enter Z, for any k,a. -/
theorem Z_no_exceptional (k a : Nat)
    (hs : 3483*(3*2^a+a+2) + 2^0*3483 + 2^0*16576 =
      2^(31114+40824*k)) : False := by
  have hbase := SheepIndependentGap.no_special_equal
    10449 3483 27025 13 5935 10
    (by decide) (by decide) (by decide) (by decide)
    (31100+40824*k) (by omega) a
  have he : 31114+40824*k = (31100+40824*k)+13+1 := by omega
  have hs' : 10449*2^a+3483*a+27025 = 2^((31100+40824*k)+13+1) := by
    rw [←he]
    have h2 : (2:Nat)^0=1 := by decide
    rw [h2] at hs
    omega
  exact hbase hs'

#print axioms Z_no_exceptional
end Sheep31104ZSpecial
