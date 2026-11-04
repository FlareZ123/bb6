import Std

namespace BB6.Agent28

/-- Exact rescaled coefficient identity at a single positive-depth inverse,
    after an arbitrary legal upper prefix. -/
theorem source_one_reset_coefficient
    (n r K P R Q u V M Fr Dr L Dp : Nat)
    (hK : K+n+3=7*P)
    (hB : R*Fr+n+2=7*P)
    (hu : R*u=n+2)
    (hP : P=R*Q)
    (hV : V+1=2*R)
    (hM : M+u=2*(n+r+2))
    (hDr : Fr+Dr+r=K+2)
    (hreset : L*Dp+r=K+Dr)
    (hRpos : 0<R) :
    L*Dp+M=(7*V)*Q := by
  have hRFr : R*Fr=K+1 := by omega
  have hprodDr := congrArg (fun z : Nat => R*z) hDr
  simp only [Nat.mul_add] at hprodDr
  have hprodReset := congrArg (fun z : Nat => R*z) hreset
  simp only [Nat.mul_add] at hprodReset
  have hprodV := congrArg (fun z:Nat => z*(K+1)) hV
  simp only [Nat.add_mul] at hprodV
  have hVK : V*(K+1)+(K+1)=2*(R*(K+1)) := by
    simpa only [Nat.mul_assoc, Nat.one_mul, Nat.mul_one] using hprodV
  have hLcoeff : R*(L*Dp)+2*(R*r)=V*(K+1) := by
    have ht : R*(K+1)=R*K+R := by simp [Nat.mul_add]
    omega
  have hprodVu := congrArg (fun z:Nat => z*u) hV
  simp only [Nat.add_mul] at hprodVu
  have hVu : V*u+u=2*(R*u) := by
    simpa only [Nat.mul_assoc, Nat.one_mul] using hprodVu
  have hMlin : M=V*u+2*r := by omega
  have hprodM := congrArg (fun z:Nat => R*z) hMlin
  have hRm : R*M=V*(n+2)+2*(R*r) := by
    calc
      _ = R*(V*u+2*r) := hprodM
      _ = V*(R*u)+2*(R*r) := by simp only [Nat.mul_add]; ac_rfl
      _ = V*(n+2)+2*(R*r) := by rw [hu]
  have hKV : V*(K+1)+V*(n+2)=V*(7*P) := by
    have hidx : (K+1)+(n+2)=K+n+3 := by omega
    have hh := congrArg (fun z:Nat=>V*z) (hidx.trans hK)
    simpa only [Nat.mul_add] using hh
  have hmul : R*(L*Dp+M)=R*((7*V)*Q) := by
    calc
      _ = R*(L*Dp)+R*M := by rw [Nat.mul_add]
      _ = V*(K+1)+V*(n+2) := by omega
      _ = V*(7*P) := hKV
      _ = R*((7*V)*Q) := by rw [hP]; ac_rfl
  exact Nat.mul_left_cancel hRpos hmul

/-- The exact dyadic remainder identity at the final upper suffix. -/
theorem source_one_reset_suffix_coefficient
    (n r l K P R L Q2 M h N V C Dp Fstar S Fend : Nat)
    (hK : K+n+3=7*P)
    (hP : P=(R*L)*Q2)
    (hreset : L*Dp+M=(7*V)*(L*Q2))
    (hM : M=L*h)
    (hN : N+h=n+r+l+1)
    (hC : C+V=R*L)
    (hFstar : Fstar+Dp+r+l=K+2)
    (hFend : S*Fend=Fstar)
    (hLpos : 0<L) :
    S*Fend+N=(7*C)*Q2 := by
  have hL : L*(Dp+h)=L*((7*V)*Q2) := by
    calc
      _ = L*Dp+L*h := by rw [Nat.mul_add]
      _ = (7*V)*(L*Q2) := by rw [← hM]; exact hreset
      _ = L*((7*V)*Q2) := by ac_rfl
  have hDp : Dp+h=(7*V)*Q2 := Nat.mul_left_cancel hLpos hL
  have hS0 : Fstar+Dp+(n+r+l+1)=7*P := by omega
  have hS1 : Fstar+N+(Dp+h)=7*P := by omega
  have hSV : (7*C)*Q2+(7*V)*Q2=7*P := by
    calc
      _ = 7*(C+V)*Q2 := by simp only [Nat.add_mul, Nat.mul_add]
      _ = 7*P := by rw [hC,hP]; ac_rfl
  omega

#print axioms BB6.Agent28.source_one_reset_coefficient
#print axioms BB6.Agent28.source_one_reset_suffix_coefficient
end BB6.Agent28
