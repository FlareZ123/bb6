import SingularLanguage
namespace SheepWeightedResidual

theorem lift_cube (r c n : Nat) (hr : 1 ≤ r)
    (base : ∃ w : Nat, 4^(3^(r-1)) = 1+3^r*(c+3^r*w)) :
    ∃ w : Nat, 4^(3^(r+n-1)) = 1+3^(r+n)*(c+3^r*w) := by
  induction n with
  | zero => simpa using base
  | succ n ih =>
    obtain ⟨w,hw⟩ := ih
    let P := 3^(r+n-1)
    let M := 3^r
    let C := c+M*w
    have hP : 3*P = 3^(r+n) := by
      dsimp [P]
      rw [← Nat.pow_succ', show (r+n-1).succ=r+n by omega]
    have hM : 3*P = M*3^n := by rw [hP,Nat.pow_add]
    have hx : 4^P = 1+3*P*C := by
      rw [hP]
      exact hw
    refine ⟨w+3^n*(C*C+P*C*C*C),?_⟩
    have hExp : 3^(r+(n+1)-1)=P*3 := by
      change 3^(r+n)=P*3
      rw [←hP,Nat.mul_comm]
    have hPow : 3^(r+(n+1))=9*P := by
      rw [show r+(n+1)=(r+n)+1 by omega,Nat.pow_succ,←hP]
      grind
    rw [hExp,Nat.pow_mul,hx,hPow]
    change (1+3*P*C)^3=1+9*P*(c+M*(w+3^n*(C*C+P*C*C*C)))
    calc
      (1+3*P*C)^3 = 1+9*P*(C+(3*P)*(C*C+P*C*C*C)) := by grind
      _ = _ := by rw [hM]; dsimp [C]; grind

theorem lift_power (M d c w q : Nat) : ∃ z : Nat,
    (1+M*d*(c+M*w))^q = 1+M*d*(c*q+M*z) := by
  induction q with
  | zero => exact ⟨0,by simp⟩
  | succ q ih =>
    obtain ⟨z,hz⟩ := ih
    refine ⟨z+w+d*(c*q+M*z)*(c+M*w),?_⟩
    rw [Nat.pow_succ,hz]
    grind

theorem lifted_exponent (r c H q : Nat) (hr : 1 ≤ r) (hH : r≤H)
    (base : ∃ w : Nat, 4^(3^(r-1)) = 1+3^r*(c+3^r*w)) :
    ∃ z : Nat, 2^(2*3^(H-1)*q)=1+3^H*(c*q+3^r*z) := by
  obtain ⟨w,hw⟩ := lift_cube r c (H-r) hr base
  rw [Nat.add_sub_of_le hH] at hw
  have hh : 3^H=3^r*3^(H-r) := by rw [←Nat.pow_add,Nat.add_sub_of_le hH]
  obtain ⟨z,hz⟩ := lift_power (3^r) (3^(H-r)) c w q
  rw [←hh,←hw] at hz
  refine ⟨z,?_⟩
  rw [Nat.pow_mul,Nat.pow_mul]
  exact hz

theorem type1_exponent_lift (H q : Nat) (hH : 3≤H) :
    ∃ z : Nat, 2^(2*3^(H-1)*q)=1+3^H*(16*q+27*z) := by
  exact lifted_exponent 3 16 H q (by decide) hH ⟨359,by decide⟩

theorem type3_exponent_lift (H q : Nat) (hH : 2≤H) :
    ∃ z : Nat, 2^(2*3^(H-1)*q)=1+3^H*(7*q+9*z) := by
  exact lifted_exponent 2 7 H q (by decide) hH ⟨0,by decide⟩

#print axioms type1_exponent_lift
#print axioms type3_exponent_lift
end SheepWeightedResidual
