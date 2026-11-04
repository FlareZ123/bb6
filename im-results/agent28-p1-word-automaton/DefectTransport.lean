import Std

namespace BB6.Agent28

/-- Exact generic dyadic defect recurrence at any positive-depth odd inverse
    step. All equalities are natural-number identities with no stochastic
    or orbit approximation. -/
theorem defect_reset_input_identity
    (n m K P B Q C F D N M V L Dp : Nat)
    (hK : K+n+3=7*P)
    (hP : P=B*Q)
    (hV : V+C=2*B)
    (hM : M+N=2*(n+m+2))
    (hF : F+N=7*Q*C)
    (hFD : F+D+m=K+2)
    (hstep : L*Dp+m=K+D) :
    L*Dp+M=7*Q*V := by
  have heq : L*Dp+F+2*m=2*K+2 := by omega
  have hL : L*Dp+M+7*Q*C=14*P := by
    have hsource : L*Dp+M+7*Q*C=L*Dp+F+2*(n+m+2) := by omega
    have hK2 : 2*(K+n+3)=14*P := by omega
    omega
  have hR : 7*Q*V+7*Q*C=14*P := by
    calc
      _ = 7*Q*(V+C) := by simp only [Nat.mul_add]
      _ = 7*Q*(2*B) := by rw [hV]
      _ = 14*P := by rw [hP]; ac_rfl
  exact Nat.add_right_cancel (hL.trans hR.symm)

/-- The same defect shape is preserved after any positive reset when its
    dyadic quotient and remainder are specified exactly. -/
theorem defect_reset_output_identity
    (n m l K P B L Q2 C Fp Dp Np M V Cp h : Nat)
    (hK : K+n+3=7*P)
    (hP : P=B*L*Q2)
    (hC : Cp+V=B*L)
    (hM : M=L*h)
    (hN : Np+h=n+m+l+1)
    (hD : L*Dp+M=7*(L*Q2)*V)
    (hF : Fp+Dp+m+l=K+2)
    (hL : 0<L) :
    Fp+Np=7*Q2*Cp := by
  have hLh : L*(Dp+h)=L*(7*Q2*V) := by
    calc
      _ = L*Dp+L*h := by simp only [Nat.mul_add]
      _ = 7*(L*Q2)*V := by rw [←hM]; exact hD
      _ = L*(7*Q2*V) := by ac_rfl
  have hDp : Dp+h=7*Q2*V := Nat.mul_left_cancel hL hLh
  have hP7 : 7*P = 7*Q2*Cp + 7*Q2*V := by
    calc
      _ = 7*(B*L*Q2) := by rw [hP]
      _ = 7*Q2*(Cp+V) := by rw [hC]; ac_rfl
      _ = 7*Q2*Cp + 7*Q2*V := by simp only [Nat.mul_add]
  have hsum : Fp+Np+Dp+h=7*P := by omega
  have hcancel : Fp+Np+7*Q2*V = 7*Q2*Cp +7*Q2*V := by omega
  exact Nat.add_right_cancel hcancel

#print axioms BB6.Agent28.defect_reset_input_identity
#print axioms BB6.Agent28.defect_reset_output_identity
end BB6.Agent28
