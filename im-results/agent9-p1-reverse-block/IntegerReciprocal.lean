import ShiftedReverseBlock

namespace BB6.Agent9IntegerReciprocal

/-- Two fixed-point reciprocals combine into an underestimate at most one
    quotient below the exact result. R and S may be calculated once for
    the fixed modulus G, block radix M and target Y. -/
theorem estimate_near (G H M Y z R S : Nat)
    (hG : 0<G) (hH : 0<H) (hz : z+1≤H)
    (hRlo : G*R≤M*H) (hRhi : M*H≤G*(R+1))
    (hSlo : G*S≤Y*H) (hShi : Y*H<G*(S+1)) :
    let b := (z*R+S)/H
    let X := M*z+Y
    b≤X/G ∧ X/G≤b+1 := by
  dsimp only
  let T := z*R+S
  let X := M*z+Y
  let b := T/H
  change b≤X/G ∧ X/G≤b+1
  have hl := Nat.mul_le_mul_right z hRlo
  have hh := Nat.mul_le_mul_right z hRhi
  have h1 : G*T≤H*X := by
    dsimp [T,X]
    rw [Nat.mul_add,Nat.mul_add]
    have he1 : G*(z*R)=(G*R)*z := by ac_rfl
    have he2 : H*(M*z)=(M*H)*z := by ac_rfl
    rw [he1,he2,Nat.mul_comm H Y]
    omega
  have h2 : H*X<G*T+G*(z+1) := by
    dsimp [T,X]
    rw [Nat.mul_add,Nat.mul_add,Nat.mul_add]
    have he1 : G*(z*R)=(G*R)*z := by ac_rfl
    have he2 : H*(M*z)=(M*H)*z := by ac_rfl
    rw [he1,he2,Nat.mul_comm H Y,Nat.mul_one]
    rw [Nat.mul_add,Nat.mul_one,Nat.add_mul] at hh
    rw [Nat.mul_add,Nat.mul_one] at hShi
    omega
  have h3 := Nat.mul_le_mul_left G hz
  have h4 : H*X<G*T+G*H := by omega
  have hd := Nat.div_add_mod T H
  have hm := Nat.mod_lt T hH
  change H*b+T%H=T at hd
  have hb : H*b≤T := by omega
  have hb' : T<H*(b+1) := by rw [Nat.mul_add,Nat.mul_one]; omega
  have hmul := Nat.mul_le_mul_left G hb
  have hmul' := Nat.mul_lt_mul_of_pos_left hb' hG
  have hlow : H*(G*b)≤H*X := by
    have he : H*(G*b)=G*(H*b) := by ac_rfl
    rw [he]; omega
  have hhi : H*X<H*(G*(b+2)) := by
    have he : H*(G*(b+2))=G*(H*(b+1))+G*H := by
      rw [show b+2=(b+1)+1 by omega,Nat.mul_add,Nat.mul_one,Nat.mul_add]
      ac_rfl
    rw [he]
    omega
  have hlow' : G*b≤X := Nat.le_of_mul_le_mul_left hlow hH
  have hhi' : X<G*(b+2) := Nat.lt_of_mul_lt_mul_left hhi
  constructor
  · exact (Nat.le_div_iff_mul_le hG).2 (by simpa [Nat.mul_comm] using hlow')
  · have h := (Nat.div_lt_iff_lt_mul hG).2 (by simpa [Nat.mul_comm] using hhi')
    omega

/-- One upward correction, no downward correction or floating fallback. -/
def correct (G X b : Nat) : Nat := if (b+1)*G≤X then b+1 else b

theorem correct_eq (G X b : Nat) (hG : 0<G) (h : b≤X/G ∧ X/G≤b+1) :
    correct G X b=X/G := by
  unfold correct
  by_cases he : (b+1)*G≤X
  · rw [if_pos he]
    have hl := (Nat.le_div_iff_mul_le hG).2 he
    omega
  · rw [if_neg he]
    have hlt := (Nat.div_lt_iff_lt_mul hG).2 (by omega : X<(b+1)*G)
    omega

#print axioms estimate_near
#print axioms correct_eq
end BB6.Agent9IntegerReciprocal
