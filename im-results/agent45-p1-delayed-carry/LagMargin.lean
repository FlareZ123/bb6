import Std
namespace BB6.Agent45.LagMargin

/-- The delayed target residue is a lower bound on the weighted offset. -/
theorem residue_le (P D v B F : Nat)
    (h : P*D*v+F = 7*P*B) : P*((7*B)%D) ≤ F := by
  have hh := congrArg (fun x => x % (P*D)) h
  have hmul : 7*P*B = P*(7*B) := by ac_rfl
  rw [hmul, Nat.mul_mod_mul_left] at hh
  have hh' : F % (P*D) = P*((7*B)%D) := by
    simpa only [Nat.mul_add_mod_self_left] using hh
  rw [← hh']
  exact Nat.mod_le _ _

/-- Any small coordinate requires a small delayed target residue. -/
theorem tail_margin (P D A L B F v : Nat)
    (hP : 0<P) (hA : A≤P)
    (hMass : P*D*v+F=7*P*B) (hF : F≤A*B)
    (hGap : A*D*L<6*P*((7*B)%D)) : L<v := by
  by_cases h : L<v
  · exact h
  · exfalso
    have hv : v≤L := by omega
    have hAB : A*B≤P*B := Nat.mul_le_mul_right B hA
    have h6 : 6*P*B≤P*D*v := by
      simp only [Nat.mul_assoc] at hMass ⊢
      omega
    have h6' : P*(6*B)≤P*(D*v) := by
      calc
        P*(6*B) = 6*P*B := by ac_rfl
        _ ≤ P*D*v := h6
        _ = P*(D*v) := by ac_rfl
    have h6B : 6*B≤D*v := Nat.le_of_mul_le_mul_left h6' hP
    have hBD : 6*B≤D*L := Nat.le_trans h6B (Nat.mul_le_mul_left D hv)
    have hr := residue_le P D v B F hMass
    have hleft : 6*(P*((7*B)%D))≤6*(A*B) := Nat.mul_le_mul_left 6 (Nat.le_trans hr hF)
    have hright := Nat.mul_le_mul_left A hBD
    have hbound : 6*P*((7*B)%D)≤A*D*L := by
      calc
        6*P*((7*B)%D) = 6*(P*((7*B)%D)) := by ac_rfl
        _ ≤ 6*(A*B) := hleft
        _ = A*(6*B) := by ac_rfl
        _ ≤ A*(D*L) := hright
        _ = A*D*L := by ac_rfl
    omega

/-- Before the delayed target arrives, divisibility of the positive offset
itself provides a coordinate margin. -/
theorem early_margin (P D A L B F v : Nat)
    (hD : 0<D) (hA : A≤P)
    (hMass : D*v+F=7*P*B) (hF : F≤A*B)
    (hDiv : D≤F) (hGap : A*L<6*P) : L<v := by
  by_cases h : L<v
  · exact h
  · exfalso
    have hv : v≤L := by omega
    have hAB : A*B≤P*B := Nat.mul_le_mul_right B hA
    have h6 : 6*P*B≤D*v := by
      simp only [Nat.mul_assoc] at hMass ⊢
      omega
    have hDA : D≤A*B := Nat.le_trans hDiv hF
    have h1 := Nat.mul_le_mul_left (6*P) hDA
    have h2 := Nat.mul_le_mul_left A h6
    have h3 := Nat.mul_le_mul_left D (Nat.mul_le_mul_left A hv)
    have hbound : D*(6*P)≤D*(A*L) := by
      calc
        D*(6*P) = 6*P*D := by ac_rfl
        _ ≤ 6*P*(A*B) := h1
        _ = A*(6*P*B) := by ac_rfl
        _ ≤ A*(D*v) := h2
        _ = D*(A*v) := by ac_rfl
        _ ≤ D*(A*L) := h3
    have := Nat.le_of_mul_le_mul_left hbound hD
    omega
end BB6.Agent45.LagMargin

#print axioms BB6.Agent45.LagMargin.tail_margin
#print axioms BB6.Agent45.LagMargin.early_margin
