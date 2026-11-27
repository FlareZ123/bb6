import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent20IndexPotential

/-- A single prepared valuation-w inverse edge, with D=L+3,
    encoded without division by D. -/
inductive Chain (L D d : Nat) : Nat → Nat → Nat → Prop
  | zero (b : Nat) : Chain L D d 0 b b
  | step {k b c f : Nat} (h : L*b = D*c + d)
      (ht : Chain L D d k c f) : Chain L D d (k+1) b f

private theorem edgePotential {L D d b c : Nat}
    (hD : D = L + 3) (h : L*b = D*c + d) :
    L * (3*b+d) = D * (3*c+d) := by
  calc
    L * (3*b+d) = 3*(L*b) + L*d := by
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm]
    _ = 3*(D*c+d) + L*d := by rw [h]
    _ = D*(3*c+d) := by
      rw [hD]
      simp [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      omega

/-- Every legal k-edge chain transports the linear potential by (L/D)^k. -/
theorem chainPotential {L D d k b f : Nat}
    (hD : D = L + 3) (h : Chain L D d k b f) :
    L^k*(3*b+d) = D^k*(3*f+d) := by
  induction h with
  | zero b => simp
  | @step j b c f hs ht ih =>
    have he := edgePotential hD hs
    calc
      L^(j+1)*(3*b+d) = L^j * (L*(3*b+d)) := by
        simp only [Nat.pow_succ]
        ac_rfl
      _ = L^j * (D*(3*c+d)) := by rw [he]
      _ = D * (L^j*(3*c+d)) := by ac_rfl
      _ = D * (D^j*(3*f+d)) := by rw [ih]
      _ = D^(j+1)*(3*f+d) := by
        simp only [Nat.pow_succ]
        ac_rfl

/-- If D and L are coprime, k valuation-w predecessors require
    the starting counter's potential to be 0 modulo D^k. -/
theorem chainDivisibility {L D d k b f : Nat}
    (hD : D = L + 3) (hc : D.Coprime L)
    (h : Chain L D d k b f) : D^k ∣ 3*b+d := by
  have hp := chainPotential hD h
  have hd : D^k ∣ L^k*(3*b+d) := ⟨3*f+d, hp⟩
  have hc' : (D^k).Coprime (L^k) :=
    (hc.pow_left k).pow_right k
  exact hc'.dvd_of_dvd_mul_left hd

/-- Each 19-adic valuation-three chain necessarily approaches -8. -/
theorem valuationThree {k b f : Nat} (h : Chain 16 19 24 k b f) :
    19^k ∣ 3*b+24 :=
  chainDivisibility (by decide) (by decide) h

/-- Each 35-adic valuation-four chain necessarily approaches -80/3. -/
theorem valuationFour {k b f : Nat} (h : Chain 32 35 80 k b f) :
    35^k ∣ 3*b+80 :=
  chainDivisibility (by decide) (by decide) h

/-- Each 67-adic valuation-five chain necessarily approaches -224/3. -/
theorem valuationFive {k b f : Nat} (h : Chain 64 67 224 k b f) :
    67^k ∣ 3*b+224 :=
  chainDivisibility (by decide) (by decide) h

#print axioms valuationThree
#print axioms valuationFour
#print axioms valuationFive
#print axioms chainPotential
#print axioms chainDivisibility
end BB6.Agent20IndexPotential
