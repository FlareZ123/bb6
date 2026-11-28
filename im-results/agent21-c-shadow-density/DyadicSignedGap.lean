import DyadicSignedPeriod
import DyadicCollision

namespace BB6.Agent21Dyadic

/-- Compatibility arithmetic does not require counters to be nonnegative:
    the signed-coordinate inverse interface obeys the same one-letter law. -/
theorem signed_one_numer (x y : Int) (r : Nat) :
    signedZ x y+offset (signedS x y) r =
      -x-y-parity (signedS x y+shift r) := by
  have hz := signed_twice_Z x y
  unfold offset
  have he : (signedS x y+parity (signedS x y))%2=0 := by
    unfold parity
    omega
  unfold signedS at hz ⊢
  omega

theorem signed_parity_cost (x y : Int) (r : Nat)
    (h : (r:Int)%2=(y+1)%2) :
    parity (signedS x y+shift r)=(x+y)%2 := by
  unfold parity signedS shift
  omega

/-- The first letter of any full completed word is precisely one of the
    direct or high inverse costs permitted by the 2-adic valuation of the
    signed target's adjusted sum. This captures the key necessity in
    the modular-cone / dyadic-word all-depth duality. -/
theorem signed_first_gap (x y : Int) (r b : Nat) (w : List Nat)
    (hr : 0<r) (hrb : r≤b)
    (hd : P b∣signedZ x y+acc (signedS x y) (r::w)) :
    (r:Int)%2=(y+1)%2 ∧ P r∣-(x+y+(x+y)%2) := by
  have hbig : P r∣signedZ x y+acc (signedS x y) (r::w) :=
    Int.dvd_trans (P_dvd r b hrb) hd
  have hfirst : P r∣signedZ x y+offset (signedS x y) r := by
    have hform : signedZ x y+acc (signedS x y) (r::w) =
        (signedZ x y+offset (signedS x y) r)+
           P r*acc (signedS x y+shift r) w := by
      simp only [acc]
      omega
    rw [hform] at hbig
    have hpart : P r∣P r*acc (signedS x y+shift r) w :=
      Int.dvd_mul_right _ _
    have hsub := Int.dvd_sub hbig hpart
    convert hsub using 1 <;> omega
  have htwo : (signedZ x y+offset (signedS x y) r)%2=0 := by
    have hh : P 1∣signedZ x y+offset (signedS x y) r :=
      Int.dvd_trans (P_dvd 1 r hr) hfirst
    simpa [P] using (Int.emod_eq_zero_of_dvd hh)
  have hpar : (r:Int)%2=(y+1)%2 := by
    rw [signed_one_numer] at htwo
    unfold parity signedS shift at htwo
    omega
  refine ⟨hpar,?_⟩
  have hq : signedZ x y+offset (signedS x y) r=-(x+y+(x+y)%2) := by
    rw [signed_one_numer,signed_parity_cost x y r hpar]
    omega
  rw [←hq]
  exact hfirst

theorem signed_first_gap_strict (x y : Int) (r b : Nat) (w : List Nat)
    (hr : 0<r) (hrb : r≤b)
    (hd : P b∣signedZ x y+acc (signedS x y) (r::w))
    (hnot : ¬P b∣-(x+y+(x+y)%2)) : r<b := by
  have hq := (signed_first_gap x y r b w hr hrb hd).2
  have hne : r≠b := by
    intro he
    subst r
    exact hnot hq
  omega

#print axioms signed_first_gap
#print axioms signed_first_gap_strict
end BB6.Agent21Dyadic
