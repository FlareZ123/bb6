import SheepOddGap
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Sheep31104THigh

private theorem K_lt_pow (a : Nat) (ha : 21 ≤ a) :
    62694*a+317461 < 2^a := by
  obtain ⟨t,rfl⟩ : ∃ t, a=21+t := ⟨a-21,by omega⟩
  induction t with
  | zero => decide
  | succ t ih =>
    have hpow : (2:Nat)^21 ≤ 2^(21+t) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hlarge : 62694 ≤ 2^(21+t) := by omega
    have he : 21+(t+1)=(21+t)+1 := by omega
    rw [he,Nat.pow_succ]
    omega

/-- All generic sources of 2-adic valuation at least 21 are impossible. -/
theorem T_generic_high (k a v : Nat) (ha : 21 ≤ a)
    (hs : 31347*(2^(a+1)+1)*v + 2*a*31347 + 2*31347 + 2*174404 =
      2^(31118+122472*k) + 3*31347) : False := by
  have hfactor : 31347*(2^(a+1)+1)*v=(2^(a+1)+1)*(31347*v) := by ac_rfl
  rw [hfactor] at hs
  have hEqNat : 2^(31118+122472*k) =
      ((2:Nat)^(a+1)+1)*(31347*v)+(62694*a+317461) := by omega
  have hEqInt : (2:Int)^(31118+122472*k) =
      ((2:Int)^(a+1)+1)*(31347*(v:Int))+(62694*(a:Int)+317461) := by
    have ht := congrArg (fun z : Nat => (z:Int)) hEqNat
    simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((31347:Nat):Int)=(31347:Int) by decide,
      show ((62694:Nat):Int)=(62694:Int) by decide,
      show ((317461:Nat):Int)=(317461:Int) by decide] using ht
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^(31118+122472*k)-(62694*(a:Int)+317461) := by
    refine ⟨31347*(v:Int),?_⟩
    omega
  have hK : 1 < (62694:Int)*(a:Int)+317461 := by omega
  have hodd : ((62694:Int)*(a:Int)+317461)%2=1 := by omega
  have hhigh : (62694:Int)*(a:Int)+317461 < (2:Int)^a := by
    have ht : ((62694*a+317461:Nat):Int)<((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr (K_lt_pow a ha)
    simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((62694:Nat):Int)=(62694:Int) by decide,
      show ((317461:Nat):Int)=(317461:Int) by decide] using ht
  exact (SheepOddGap.no_power_signed_small_odd a
    (62694*(a:Int)+317461) hK hodd hhigh (31118+122472*k)).1 hdiv

#print axioms K_lt_pow
#print axioms T_generic_high
end Sheep31104THigh
