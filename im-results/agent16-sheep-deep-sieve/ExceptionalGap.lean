import Std

namespace SheepExceptional

private theorem pow_two_positive (n : Nat) : 0 < (2:Int)^n := Int.pow_pos (by decide)

private theorem pow_two_le (a b : Nat) (h : a ≤ b) : (2:Int)^a ≤ (2:Int)^b := by
  have hp : (2:Nat)^a ≤ (2:Nat)^b := Nat.pow_le_pow_right (by decide) h
  exact_mod_cast hp

private theorem pow_two_add (a b : Nat) : (2:Int)^(a+b) = (2:Int)^a * (2:Int)^b := by
  exact Int.pow_add 2 a b

/-- The high and low signed gap conditions, once true, exclude all special
predecessors of a symbolic Sheep inverse-family target. -/
theorem no_special_predecessor
    (d b : Int) (s h j a : Nat) (hd : 0 < d) (hj : h+1 ≤ j)
    (hlo : (3*d-(2:Int)^(s+h))*(2:Int)^j > (2:Int)^h*b)
    (hhi : ((2:Int)^(s+h+1)-3*d)*(2:Int)^j >
      (2:Int)^(h+1)*(d*((j:Int)+3)-b)) :
    (2:Int)^(j+s)+b ≠ d*(3*(2:Int)^a+(a:Int)+3) := by
  intro heq
  have pH : 0<(2:Int)^h := pow_two_positive h
  have pH1 : 0<(2:Int)^(h+1) := pow_two_positive (h+1)
  have pJ : 0<(2:Int)^j := pow_two_positive j
  have pA : 0<(2:Int)^a := pow_two_positive a
  have hpSJ : (2:Int)^(j+s)=(2:Int)^j*(2:Int)^s := pow_two_add j s
  have hpSH : (2:Int)^(s+h)=(2:Int)^s*(2:Int)^h := pow_two_add s h
  have hpSH1 : (2:Int)^(s+h+1)=(2:Int)^s*(2:Int)^(h+1) := by
    have he : s+h+1=s+(h+1) := by omega
    rw [he,pow_two_add]
  have hpH1 : (2:Int)^(h+1)=2*(2:Int)^h := by
    rw [Int.pow_succ]
    ac_rfl
  by_cases ha : j-h ≤ a
  · have hjdiff : j-h+h=j := by omega
    have hhpow : (2:Int)^j ≤ (2:Int)^h*(2:Int)^a := by
      have pp := pow_two_le (j-h) a ha
      have hmul := Int.mul_le_mul_of_nonneg_left pp (show 0≤(2:Int)^h by omega)
      rw [←pow_two_add] at hmul
      rw [Nat.add_comm h (j-h), hjdiff] at hmul
      exact hmul
    have hident : (3*d-(2:Int)^(s+h))*(2:Int)^j =
      (3*d)*(2:Int)^j - (2:Int)^h*(2:Int)^(j+s) := by
      rw [hpSH,hpSJ,Int.sub_mul]
      congr 1
      ac_rfl
    rw [hident] at hlo
    have hpos_a : 0≤(a:Int)+3 := by omega
    have hpowmul := Int.mul_le_mul_of_nonneg_left hhpow (show 0≤3*d by omega)
    have hterm : 0 ≤ ((2:Int)^h*d)*((a:Int)+3) :=
      Int.mul_nonneg (Int.mul_nonneg (by omega) (by omega)) hpos_a
    have hsource : (2:Int)^h*(d*(3*(2:Int)^a+(a:Int)+3)) =
      (3*d)*((2:Int)^h*(2:Int)^a) +
      ((2:Int)^h*d)*((a:Int)+3) := by
      have regroup : 3*(2:Int)^a+(a:Int)+3 =
        3*(2:Int)^a+((a:Int)+3) := by omega
      rw [regroup]
      calc
        _ = ((2:Int)^h*d)*(3*(2:Int)^a+((a:Int)+3)) := by ac_rfl
        _ = ((2:Int)^h*d)*(3*(2:Int)^a)+
            ((2:Int)^h*d)*((a:Int)+3) := by rw [Int.mul_add]
        _ = (3*d)*((2:Int)^h*(2:Int)^a)+
            ((2:Int)^h*d)*((a:Int)+3) := by congr 1; ac_rfl
    have htarget : (2:Int)^h*((2:Int)^(j+s)+b) =
      (2:Int)^h*(2:Int)^(j+s)+(2:Int)^h*b := by
      rw [Int.mul_add]
    rw [heq] at htarget
    rw [hsource] at htarget
    omega
  · have hal : a+h+1 ≤ j := by omega
    have hhpow : (2:Int)^(h+1)*(2:Int)^a ≤ (2:Int)^j := by
      have pp := pow_two_le (a+(h+1)) j hal
      simpa [pow_two_add,Nat.add_comm,Int.mul_comm] using pp
    have hjA : (a:Int) ≤ (j:Int) := by exact_mod_cast (show a≤j by omega)
    have hident : ((2:Int)^(s+h+1)-3*d)*(2:Int)^j =
      (2:Int)^(h+1)*(2:Int)^(j+s) - (3*d)*(2:Int)^j := by
      rw [hpSH1,hpSJ,Int.sub_mul]
      congr 1
      ac_rfl
    rw [hident] at hhi
    have hmul := Int.mul_le_mul_of_nonneg_left hhpow (show 0≤3*d by omega)
    have hcoeff : 0 ≤ (2:Int)^(h+1)*d :=
      Int.mul_nonneg (show 0≤(2:Int)^(h+1) by omega) (show 0≤d by omega)
    have hlinmul := Int.mul_le_mul_of_nonneg_left
      (show (a:Int)+3≤(j:Int)+3 by omega) hcoeff
    have hright : (2:Int)^(h+1)*(d*((j:Int)+3)-b) =
      ((2:Int)^(h+1)*d)*((j:Int)+3) - (2:Int)^(h+1)*b := by
      rw [Int.mul_sub]
      congr 1
      ac_rfl
    rw [hright] at hhi
    have hsource : (2:Int)^(h+1)*(d*(3*(2:Int)^a+(a:Int)+3)) =
      (3*d)*((2:Int)^(h+1)*(2:Int)^a) +
      ((2:Int)^(h+1)*d)*((a:Int)+3) := by
      have regroup : 3*(2:Int)^a+(a:Int)+3 =
        3*(2:Int)^a+((a:Int)+3) := by omega
      rw [regroup]
      calc
        _ = ((2:Int)^(h+1)*d)*(3*(2:Int)^a+((a:Int)+3)) := by ac_rfl
        _ = ((2:Int)^(h+1)*d)*(3*(2:Int)^a)+
            ((2:Int)^(h+1)*d)*((a:Int)+3) := by rw [Int.mul_add]
        _ = (3*d)*((2:Int)^(h+1)*(2:Int)^a)+
            ((2:Int)^(h+1)*d)*((a:Int)+3) := by congr 1; ac_rfl
    have htarget : (2:Int)^(h+1)*((2:Int)^(j+s)+b) =
      (2:Int)^(h+1)*(2:Int)^(j+s)+(2:Int)^(h+1)*b := by
      rw [Int.mul_add]
    rw [heq] at htarget
    rw [hsource] at htarget
    omega

#print axioms no_special_predecessor
end SheepExceptional
