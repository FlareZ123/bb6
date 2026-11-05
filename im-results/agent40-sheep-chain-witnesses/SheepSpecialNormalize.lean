import Std

namespace SheepSpecialNormalize

/-- Pure semiring identity identifying the exceptional Sheep inverse branch
with the exponential-versus-linear gap certificates. -/
theorem expand (D P a : Nat) :
    D*(3*2^a+a+2)+P=(3*D)*2^a+D*a+(2*D+P) := by
  simp only [Nat.mul_add, Nat.mul_assoc]
  ac_rfl

theorem normalize (d c h a n : Nat)
    (heq : (d*3^h)*(3*2^a+a+2)+2^h*d+2^h*c=2^n) :
    (3*(d*3^h))*2^a+(d*3^h)*a+
      (2*(d*3^h)+2^h*(d+c))=2^n := by
  let D := d*3^h
  let P := 2^h*(d+c)
  have hP : 2^h*d+2^h*c=P := by dsimp [P]; rw [Nat.mul_add]
  have heq2 : D*(3*2^a+a+2)+P=2^n := by
    dsimp [D] at *
    omega
  have he := expand D P a
  dsimp [D,P] at he ⊢
  omega

#print axioms normalize
end SheepSpecialNormalize
