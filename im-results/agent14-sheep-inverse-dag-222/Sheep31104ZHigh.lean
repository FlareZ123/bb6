import SheepOddGap
set_option maxRecDepth 32768
set_option maxHeartbeats 0

namespace Sheep31104ZHigh

/-- All valuations above 17 satisfy the signed odd-remainder gap. -/
private theorem K_lt_pow (a : Nat) (ha : 18 ≤ a) :
    6966*a+29669 < 2^a := by
  obtain ⟨t,rfl⟩ : ∃ t, a=18+t := ⟨a-18,by omega⟩
  induction t with
  | zero => decide
  | succ t ih =>
    have hpow : (2:Nat)^18 ≤ 2^(18+t) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hlarge : 6966 ≤ 2^(18+t) := by omega
    have he : 18+(t+1)=(18+t)+1 := by omega
    rw [he,Nat.pow_succ]
    omega

/-- Unbounded generic source valuations cannot enter Z. -/
theorem Z_generic_high (k a v : Nat) (ha : 18 ≤ a)
    (hs : 3483*(2^(a+1)+1)*v + 2*a*3483 + 2*3483 + 2*16576 =
      2^(31115+40824*k) + 3*3483) : False := by
  have hfactor : 3483*(2^(a+1)+1)*v=(2^(a+1)+1)*(3483*v) := by ac_rfl
  rw [hfactor] at hs
  have hEqNat : 2^(31115+40824*k) =
      ((2:Nat)^(a+1)+1)*(3483*v)+(6966*a+29669) := by omega
  have hEqInt : (2:Int)^(31115+40824*k) =
      ((2:Int)^(a+1)+1)*(3483*(v:Int))+(6966*(a:Int)+29669) := by
    have ht := congrArg (fun z : Nat => (z:Int)) hEqNat
    simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((1:Nat):Int)=(1:Int) by decide,
      show ((3483:Nat):Int)=(3483:Int) by decide,
      show ((6966:Nat):Int)=(6966:Int) by decide,
      show ((29669:Nat):Int)=(29669:Int) by decide] using ht
  have hdiv : ((2:Int)^(a+1)+1) ∣
      (2:Int)^(31115+40824*k)-(6966*(a:Int)+29669) := by
    refine ⟨3483*(v:Int),?_⟩
    omega
  have hK : 1 < (6966:Int)*(a:Int)+29669 := by omega
  have hodd : ((6966:Int)*(a:Int)+29669)%2=1 := by omega
  have hhigh : (6966:Int)*(a:Int)+29669 < (2:Int)^a := by
    have ht : ((6966*a+29669:Nat):Int)<((2:Nat)^a:Int) :=
      Int.ofNat_lt.mpr (K_lt_pow a ha)
    simpa only [Int.natCast_pow, Int.natCast_add, Int.natCast_mul,
      show ((2:Nat):Int)=(2:Int) by decide,
      show ((6966:Nat):Int)=(6966:Int) by decide,
      show ((29669:Nat):Int)=(29669:Int) by decide] using ht
  exact (SheepOddGap.no_power_signed_small_odd a
    (6966*(a:Int)+29669) hK hodd hhigh (31115+40824*k)).1 hdiv

#print axioms K_lt_pow
#print axioms Z_generic_high
end Sheep31104ZHigh
