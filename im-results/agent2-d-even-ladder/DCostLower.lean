import Lean.Elab.Tactic.Omega

namespace BB6.DCostLower

def cost (k q : Nat) : Nat := 12*k*k+49*k+58+6*q

def kIndex : Nat → Nat → Nat
  | 0, u => u
  | m+1, u => 3*kIndex m u+2

def totalCost : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | m+1, u, q => cost (kIndex (m+1) u) q + totalCost m (8*u+7) (q+2)

private theorem base_poly (u : Nat) :
    (3*u+2)*(3*u+2) = 9*(u*u)+12*u+4 := by
  have hm : (3*u)*(3*u) = 9*(u*u) := by ac_rfl
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, hm]
  omega

private theorem square_poly (u : Nat) :
    (u+1)*(u+1) = u*u+2*u+1 := by
  simp only [Nat.add_mul,Nat.mul_add]
  omega

theorem cost_base_ge (u q : Nat) :
    64*(u+1)*(u+1) ≤ cost (3*u+2) q := by
  rw [Nat.mul_assoc 64 (u+1) (u+1)]
  rw [square_poly]
  simp only [cost]
  rw [Nat.mul_assoc 12 (3*u+2) (3*u+2)]
  rw [base_poly]
  omega

/-- In an arbitrary synthetic E ladder of depth m+1, the primitive
    runtime grows at least as 64^(m+1)*(u+1)^2. This uses only the exact
    recursive source time formula and positivity, no asymptotic estimates. -/
theorem totalCost_ge (m u q : Nat) :
    64^(m+1)*(u+1)*(u+1) ≤ totalCost (m+1) u q := by
  induction m generalizing u q with
  | zero =>
    change 64*(u+1)*(u+1) ≤ cost (3*u+2) q
    exact cost_base_ge u q
  | succ m ih =>
    have hscale :
        64^(m+2)*(u+1)*(u+1) =
          64^(m+1)*(8*u+8)*(8*u+8) := by
      have he : 8*u+8 = 8*(u+1) := by omega
      rw [he]
      have h64 : 64^(m+2)=64*64^(m+1) := by
        rw [show m+2=(m+1)+1 by omega, Nat.pow_succ]
        ac_rfl
      rw [h64]
      have ht : 64 = 8*8 := by decide
      rw [ht]
      ac_rfl
    calc
      64^((m+1)+1)*(u+1)*(u+1) =
          64^(m+1)*(8*u+8)*(8*u+8) := by
            simpa [show (m+1)+1=m+2 by omega] using hscale
      _ ≤ totalCost (m+1) (8*u+7) (q+2) := by
        simpa [show 8*u+7+1=8*u+8 by omega] using ih (8*u+7) (q+2)
      _ ≤ totalCost ((m+1)+1) u q := by
        change totalCost (m+1) (8*u+7) (q+2) ≤
          cost (kIndex (m+2) u) q + totalCost (m+1) (8*u+7) (q+2)
        omega

theorem totalCost_ge_64pow (m u q : Nat) (h : 0 < m) :
    64^m ≤ totalCost m u q := by
  cases m with
  | zero => omega
  | succ m =>
    have hcore := totalCost_ge m u q
    have h1 : 0 < u+1 := by omega
    have hh : 64^(m+1) ≤ 64^(m+1)*(u+1)*(u+1) := by
      have hfactor : 1 ≤ (u+1)*(u+1) := by
        have hmul := Nat.mul_le_mul h1 h1
        omega
      have hpow : 0 ≤ 64^(m+1) := Nat.zero_le _
      have hm := Nat.mul_le_mul_left (64^(m+1)) hfactor
      simpa [Nat.mul_assoc] using hm
    omega

#print axioms cost_base_ge
#print axioms totalCost_ge
#print axioms totalCost_ge_64pow
end BB6.DCostLower
