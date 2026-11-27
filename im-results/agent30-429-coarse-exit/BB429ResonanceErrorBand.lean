import BB429ResonanceError

namespace BB429.CoarseExit

set_option maxHeartbeats 20000000

/-- Pure arithmetic core of the remaining d=234 resonance.  The hypotheses
    are exactly the coarse information supplied by a minimal base-four
    resonance word: b is between h/4 and (h-1)/3, b is large compared with
    its digit length, and 9b=208m+1981.  The detailed word disappears.

    If x,z are the U/V low-order errors after the resonant block prefix and
    dc is three times the rotated low-side deviation, then dc is squeezed
    strictly between the two scale rays needed for the final low-cycle
    evacuation. -/
theorem d234_error_band_arith
    (i m : Nat) (b h y x z dc : Int)
    (hi : 7≤i)
    (hb0 : 0≤b)
    (hlo : 500*(i:Int)≤b)
    (hbig : 3500≤b)
    (hhlo : h≤4*b)
    (hh0 : 0≤h)
    (hhhi : 3*b+1≤h)
    (hrel : 9*b=208*(m:Int)+1981)
    (hy : y=108*(m:Int)+777-18*(i:Int))
    (hxlo : (-2*(y+42*(i:Int))+6)*b≤x)
    (hxhi : x≤(-2*y+54)*b)
    (hzlo : y+18*(i:Int)≤z)
    (hzhi : z≤y+42*(i:Int))
    (hdc : dc=-6*x+4*z+12) :
    54*h*h < 16*dc ∧ 4*dc≤27*h*h := by
  have hm3 : 3*(i:Int)≤(m:Int) := by
    omega
  have hy0 : 0≤y := by
    rw [hy]
    omega
  have hcoefL : 0≤48*(m:Int)-216*(i:Int)-2886 := by
    omega
  have hidL :
      12*y-324-54*b = 48*(m:Int)-216*(i:Int)-2886 := by
    rw [hy]
    grind +ring
  have hxhi6 := Int.mul_le_mul_of_nonpos_left hxhi (by decide : (-6:Int)≤0)
  have hzlo4 := Int.mul_le_mul_of_nonneg_left hzlo (by decide : (0:Int)≤4)
  have hdlower :
      (12*y-324)*b+4*y+72*(i:Int)+12 ≤ dc := by
    rw [hdc]
    grind +ring
  have hL54 : 54*b*b < (12*y-324)*b+4*y+72*(i:Int)+12 := by
    have hcb : 0≤(12*y-324-54*b)*b := by
      rw [hidL]
      exact Int.mul_nonneg hcoefL hb0
    omega
  have hD54 : 54*b*b < dc := lt_of_lt_of_le hL54 hdlower
  have hb4 : 0≤4*b := by omega
  have hs1 := Int.mul_le_mul_of_nonneg_left hhlo hh0
  have hs2 := Int.mul_le_mul_of_nonneg_right hhlo hb4
  have hsquare : h*h≤16*b*b := by
    calc
      h*h ≤ h*(4*b) := hs1
      _ ≤ (4*b)*(4*b) := by
        simpa [Int.mul_comm] using hs2
      _ = 16*b*b := by ring
  have hlower : 54*h*h < 16*dc := by
    have hs := Int.mul_le_mul_of_nonneg_left hsquare (by decide : (0:Int)≤54)
    have hd := Int.mul_lt_mul_of_pos_left hD54 (by decide : (0:Int)<16)
    omega

  have hcoefU : 16000≤432*(m:Int)+16335-1152*(i:Int) := by
    omega
  have htailU : 16*y+672*(i:Int)+48≤16000*b := by
    rw [hy]
    omega
  have hidU :
      243*b-(48*y+2016*(i:Int)-144) =
        432*(m:Int)+16335-1152*(i:Int) := by
    rw [hy]
    grind +ring
  have hxlo6 := Int.mul_le_mul_of_nonpos_left hxlo (by decide : (-6:Int)≤0)
  have hzhi4 := Int.mul_le_mul_of_nonneg_left hzhi (by decide : (0:Int)≤4)
  have hdupper :
      dc≤(12*y+504*(i:Int)-36)*b+4*y+168*(i:Int)+12 := by
    rw [hdc]
    grind +ring
  have hcoefUb : 16000*b≤
      (432*(m:Int)+16335-1152*(i:Int))*b := by
    exact Int.mul_le_mul_of_nonneg_right hcoefU hb0
  have hU243 :
      4*((12*y+504*(i:Int)-36)*b+4*y+168*(i:Int)+12)≤243*b*b := by
    rw [←hidU] at hcoefUb
    grind +ring
  have hD243 : 4*dc≤243*b*b := by
    have h4 := Int.mul_le_mul_of_nonneg_left hdupper (by decide : (0:Int)≤4)
    omega
  have h3b : 3*b≤h := by omega
  have h3b0 : 0≤3*b := by omega
  have ht1 := Int.mul_le_mul_of_nonneg_left h3b h3b0
  have ht2 := Int.mul_le_mul_of_nonneg_right h3b hh0
  have hbsquare : 9*b*b≤h*h := by
    calc
      (3*b)*(3*b) ≤ h*(3*b) := by
        simpa [Int.mul_comm] using ht1
      _ ≤ h*h := ht2
      _ = h*h := rfl
  have hs := Int.mul_le_mul_of_nonneg_left hbsquare (by decide : (0:Int)≤27)
  constructor
  · exact hlower
  · omega

#print axioms d234_error_band_arith

end BB429.CoarseExit
