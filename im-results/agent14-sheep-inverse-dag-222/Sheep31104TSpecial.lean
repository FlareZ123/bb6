import IndependentExceptionalGap
namespace Sheep31104TSpecial

theorem T_no_exceptional (k a : Nat)
    (hs : 31347*(3*2^a+a+2) + 2^0*31347 + 2^0*174404 =
      2^(31117+122472*k)) : False := by
  have hbase := SheepIndependentGap.no_special_equal
    94041 31347 268445 16 37031 10
    (by decide) (by decide) (by decide) (by decide)
    (31100+122472*k) (by omega) a
  have he : 31117+122472*k = (31100+122472*k)+16+1 := by omega
  have hs' : 94041*2^a+31347*a+268445 = 2^((31100+122472*k)+16+1) := by
    rw [←he]
    have h2 : (2:Nat)^0=1 := by decide
    rw [h2] at hs
    omega
  exact hbase hs'
#print axioms T_no_exceptional
end Sheep31104TSpecial
