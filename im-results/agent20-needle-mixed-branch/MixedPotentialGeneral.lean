import Mathlib

namespace BB6.Agent20MixedPotentialGeneral

/-- Any two monochromatic inverse labels compete through their affine
    fixed-point potentials. No coprimality or machine semantics is required. -/
theorem gap_from_potential {L D d a M k B P : Nat}
    (hpot : L^k*(3*B+d) = D^k*(3*P+d))
    (hB : M ∣ 3*B+a) (hP : M ∣ 3*P+a) :
    (M : Int) ∣
      ((D : Int)^k-(L : Int)^k) * ((a : Int)-(d : Int)) := by
  rcases hB with ⟨x, hx⟩
  rcases hP with ⟨y, hy⟩
  have hp : (L : Int)^k*(3*(B : Int)+(d : Int)) =
      (D : Int)^k*(3*(P : Int)+(d : Int)) := by
    exact_mod_cast hpot
  have hBx : 3*(B : Int)+(a : Int) = (M : Int)*(x : Int) := by
    exact_mod_cast hx
  have hPy : 3*(P : Int)+(a : Int) = (M : Int)*(y : Int) := by
    exact_mod_cast hy
  refine ⟨(D : Int)^k*(y : Int)-(L : Int)^k*(x : Int), ?_⟩
  calc
    ((D : Int)^k-(L : Int)^k)*((a : Int)-(d : Int)) =
      (D : Int)^k*(3*(P : Int)+(a : Int)) -
      (L : Int)^k*(3*(B : Int)+(a : Int)) := by
        linear_combination hp
    _ = (M : Int)*((D : Int)^k*(y : Int)-(L : Int)^k*(x : Int)) := by
      rw [hBx, hPy]
      ring

/-- Single inverse step: the gap is always the product 3(a-d). -/
theorem immediate_gap {L D d a M B P : Nat}
    (hD : D=L+3)
    (hedge : L*B=D*P+d)
    (hB : M ∣ 3*B+a) (hP : M ∣ 3*P+a) :
    (M : Int) ∣ 3*((a : Int)-(d : Int)) := by
  have hpot : L*(3*B+d)=D*(3*P+d) := by
    calc
      L*(3*B+d) = 3*(L*B)+L*d := by ring
      _ = 3*(D*P+d)+L*d := by rw [hedge]
      _ = D*(3*P+d) := by
        rw [hD]
        ring
  have hgap := gap_from_potential (L:=L) (D:=D) (d:=d)
    (a:=a) (M:=M) (k:=1) (B:=B) (P:=P)
    (by simpa using hpot) hB hP
  have hDInt : (D : Int) = (L : Int) + 3 := by
    exact_mod_cast hD
  have hpow : (D : Int)^1 - (L : Int)^1 = 3 := by
    simp [hDInt]
  rw [hpow] at hgap
  exact hgap

/-- A one-step transfer of another valuation's affine potential. -/
theorem cross_step_identity {L D d a B P : Nat}
    (hD : D=L+3)
    (hp : L*(3*B+d)=D*(3*P+d)) :
    (D : Int)*(3*(P : Int)+(a : Int)) =
    (L : Int)*(3*(B : Int)+(a : Int)) +
      3*((a : Int)-(d : Int)) := by
  have hI : (L : Int)*(3*(B : Int)+(d : Int)) =
      (D : Int)*(3*(P : Int)+(d : Int)) := by
    exact_mod_cast hp
  have hDI : (D : Int)=(L : Int)+3 := by
    exact_mod_cast hD
  rw [hDI] at hI ⊢
  linear_combination -hI

#print axioms cross_step_identity

#print axioms gap_from_potential
#print axioms immediate_gap
end BB6.Agent20MixedPotentialGeneral
