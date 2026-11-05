import FirstForkFourResidues
set_option maxHeartbeats 0
set_option maxRecDepth 16384

/- Exact elementary 3-adic power lifting needed to show that no finite
    bound on the fatal-input valuation can be valid. -/
namespace CascadeFatalValuation

private theorem cube (z:Nat):(1+z)^3=1+3*z+3*z^2+z^3:=by
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.mul_one,Nat.one_mul,Nat.add_mul,Nat.mul_add]
  omega
private theorem square (x y:Nat):(3*x*y)^2=9*x^2*y^2:=by
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
  simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
private theorem third (x y:Nat):(3*x*y)^3=27*x^3*y^3:=by
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul]
  simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
private theorem cube_identity (x y:Nat):
  (1+3*x*y)^3=1+9*x*(y+3*x*y^2+3*x^2*y^3):=by
  rw [cube,square,third]
  simp only [Nat.pow_succ,Nat.pow_zero,Nat.one_mul,Nat.mul_one,Nat.mul_add,Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
  simp only [show (3:Nat)*3=9 by decide, show (3:Nat)*9=27 by decide]
  ac_rfl

/-- The special exponent 3^k gives 4^(3^k) = 1 (mod 3^(k+1)). -/
theorem power_three_lift (k : Nat) : ∃ m : Nat,
    4^(3^k)=1+3^(k+1)*m := by
  induction k with
  | zero => exact ⟨1,by decide⟩
  | succ k ih =>
    obtain ⟨m,hm⟩:=ih
    let P:=3^k
    have hstep:3^(k+1)=3*P:=by
      dsimp [P]
      rw [Nat.pow_succ]
      omega
    have hpow:4^(3^(k+1))=(4^P)^3:=by
      have he:3^(k+1)=P*3:=by
        dsimp [P]
        rw [Nat.pow_succ]
      rw [he,Nat.pow_mul]
    refine ⟨m+3*P*m^2+3*P^2*m^3,?_⟩
    have he:3^(k+1+1)=9*P:=by
      dsimp [P]
      rw [Nat.pow_add]
      simp only [Nat.pow_one]
      rw [Nat.pow_succ]
      omega
    rw [hpow,hm,hstep,he]
    exact cube_identity P m

private theorem mul_identity (P v m:Nat):
    (1+3*P*v)*(1+3*P*m)=1+3*P*(v+m+3*P*v*m):=by
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_comm,Nat.mul_left_comm]
  ac_rfl

theorem one_plus_division (P m j:Nat):
    ∃q:Nat,(1+3*P*m)^j=1+3*P*q :=by
  induction j with
  | zero=>exact ⟨0,by simp⟩
  | succ j ih=>
    obtain ⟨q,hq⟩:=ih
    refine ⟨q+m+3*P*q*m,?_⟩
    rw [Nat.pow_succ,hq]
    exact mul_identity P q m

/-- Every shift by an integral multiple of 2·3^k leaves powers of two
    congruent to one modulo 3^(k+1). -/
theorem pow_offset (k j:Nat):∃m:Nat,
    2^(2*3^k*j)=1+3*3^k*m :=by
  obtain ⟨m,hm⟩:=power_three_lift k
  have hb:2^(2*3^k)=1+3*3^k*m:=by
    rw [Nat.pow_mul,show (2:Nat)^2=4 by decide]
    have he:3^(k+1)=3*3^k:=by
      rw [Nat.pow_succ]
      omega
    rw [←he]
    exact hm
  obtain ⟨q,hq⟩:=one_plus_division (3^k) m j
  refine ⟨q,?_⟩
  rw [show 2*3^k*j=(2*3^k)*j by omega,Nat.pow_mul,hb]
  exact hq

#print axioms power_three_lift
#print axioms pow_offset
end CascadeFatalValuation
