import ExceptionalGap
import ExceptionalGrowth

namespace SheepExceptional

private theorem pow_two_le (a b : Nat) (h : a ≤ b) : (2:Int)^a ≤ (2:Int)^b := by
  have hp : (2:Nat)^a ≤ (2:Nat)^b := Nat.pow_le_pow_right (by decide) h
  exact_mod_cast hp

/-- A finite integer certificate at exponent J excludes every exceptional
Sheep inverse at every larger exponent, without any exponent cutoff. -/
theorem uniform_special_parent_absent
    (d b : Int) (s h J : Nat)
    (hd : 0 < d) (hstart : h+1 ≤ J)
    (hLcoef : 0 ≤ 3*d-(2:Int)^(s+h))
    (hUcoef : 0 ≤ (2:Int)^(s+h+1)-3*d)
    (hLbase : (3*d-(2:Int)^(s+h))*(2:Int)^J > (2:Int)^h*b)
    (hUbase : ((2:Int)^(s+h+1)-3*d)*(2:Int)^J >
       (2:Int)^(h+1)*(d*((J:Int)+3)-b))
    (hSlope : (2:Int)^(h+1)*d ≤
       ((2:Int)^(s+h+1)-3*d)*(2:Int)^J) :
    ∀ j ≥ J, ∀ a : Nat,
      (2:Int)^(j+s)+b ≠ d*(3*(2:Int)^a+(a:Int)+3) := by
  intro j hj a
  have hP : (2:Int)^J ≤ (2:Int)^j := pow_two_le J j hj
  have hLP := Int.mul_le_mul_of_nonneg_left hP hLcoef
  have hLower : (3*d-(2:Int)^(s+h))*(2:Int)^j > (2:Int)^h*b := by omega
  let H : Int := (2:Int)^(h+1)
  let U : Int := (2:Int)^(s+h+1)-3*d
  let B : Int := H*d
  let C : Int := H*(3*d-b)
  have hRewrite (k : Nat) :
      H*(d*((k:Int)+3)-b) = B*(k:Int)+C := by
    dsimp [B,C]
    calc
      H*(d*((k:Int)+3)-b) = (H*d)*((k:Int)+3)-H*b := by
        rw [Int.mul_sub]
        congr 1
        ac_rfl
      _ = ((H*d)*(k:Int)+(H*d)*3)-H*b := by rw [Int.mul_add]
      _ = (H*d)*(k:Int)+H*(3*d-b) := by
        rw [Int.mul_sub]
        have hh : (H*d)*3 = H*(3*d) := by ac_rfl
        rw [hh]
        omega
  have hUbase' : B*(J:Int)+C < U*(2:Int)^J := by
    have hh := hRewrite J
    dsimp [H,U] at hh ⊢
    omega
  have hSlope' : B ≤ U*(2:Int)^J := by
    dsimp [B,U,H]
    exact hSlope
  have hAll := binary_dominates_linear U B C J hUcoef hUbase' hSlope' (j-J)
  have hjeq : J+(j-J)=j := by omega
  have hcast : (J:Int)+(↑(j-J):Int)=(j:Int) := by exact_mod_cast hjeq
  rw [hcast,hjeq] at hAll
  have hUpper : ((2:Int)^(s+h+1)-3*d)*(2:Int)^j >
      (2:Int)^(h+1)*(d*((j:Int)+3)-b) := by
    have hh := hRewrite j
    dsimp [U,H] at hAll hh
    omega
  exact no_special_predecessor d b s h j a hd (by omega) hLower hUpper

#print axioms uniform_special_parent_absent
end SheepExceptional
