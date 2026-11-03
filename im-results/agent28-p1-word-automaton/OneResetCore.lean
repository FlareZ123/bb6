import Std

namespace BB6.Agent28

private theorem mul_semiring_id (N x : Nat) :
    N + 2*N*(12*x+1) = N*(24*x+3) := by
  simp only [Nat.mul_add]
  have hp : N*(24*x) = (2*N)*(12*x) := by
    simp only [show (24:Nat)=2*12 by decide]
    ac_rfl
  omega

-- Pure numerical contradiction; source transport remains a separate obligation.
theorem bounded_one_reset_wall_impossible
    (n x P R L N S C m : Nat)
    (hx : x = n+2)
    (hR : R ≤ x) (hL : L ≤ 4*x) (hN : N ≤ 6*x)
    (hS : S ≤ N) (hm : m ≤ 11*x) (hC : 1 ≤ C)
    (heq : 7*P*C = R*L*(N+2*S*(m+n+3)))
    (hbound : 24*x^3*(24*x+3) < 7*P) : False := by
  have hmn : m+n+3 ≤ 12*x+1 := by omega
  have hS2 : 2*S ≤ 2*N := Nat.mul_le_mul_left 2 hS
  have hprod1 : (2*S)*(m+n+3) ≤ (2*N)*(m+n+3) :=
    Nat.mul_le_mul_right (m+n+3) hS2
  have hprod2 : (2*N)*(m+n+3) ≤ (2*N)*(12*x+1) :=
    Nat.mul_le_mul_left (2*N) hmn
  have hmid : N+2*S*(m+n+3) ≤ N*(24*x+3) := by
    calc
      _ ≤ N+(2*N)*(m+n+3) := Nat.add_le_add_left hprod1 N
      _ ≤ N+(2*N)*(12*x+1) := Nat.add_le_add_left hprod2 N
      _ = N*(24*x+3) := mul_semiring_id N x
  have hRL : R*L ≤ 4*x^2 := by
    have hh := Nat.mul_le_mul hR hL
    calc
      _ ≤ x*(4*x) := hh
      _ = 4*x^2 := by
        simp [Nat.pow_succ, ← Nat.mul_assoc]
        ac_rfl
  have hprod3 : N*(24*x+3) ≤ (6*x)*(24*x+3) :=
    Nat.mul_le_mul_right (24*x+3) hN
  have hsum : R*L*(N+2*S*(m+n+3)) ≤ 24*x^3*(24*x+3) := by
    calc
      _ ≤ (4*x^2)*(N*(24*x+3)) := Nat.mul_le_mul hRL hmid
      _ ≤ (4*x^2)*((6*x)*(24*x+3)) := Nat.mul_le_mul_left (4*x^2) hprod3
      _ = (4*6)*(x^3*(24*x+3)) := by
        simp only [Nat.pow_succ, Nat.pow_zero]
        ac_rfl
      _ = 24*x^3*(24*x+3) := by
        simp [Nat.mul_assoc]

  have hCmul : 7*P ≤ 7*P*C := by
    have hh := Nat.mul_le_mul_left (7*P) hC
    simpa using hh
  omega

#print axioms BB6.Agent28.bounded_one_reset_wall_impossible
end BB6.Agent28
