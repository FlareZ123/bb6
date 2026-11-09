import Std
namespace BB6.Agent50Cost

def shift (t n : Nat) : Nat := (t % 2) * n

theorem algebraic_duality (p n H Hc X Xc q t : Nat)
    (hp : p = 2*n)
    (hH : H + Hc + 1 = 3*p)
    (hX : X + Xc + 3 = t*n) :
    (p ∣ (3+8*H)*q + 1+X) ↔
    (p ∣ (5+8*Hc)*(q+shift t n)+2+Xc) := by
  let d := t%2
  have hd : t=2*(t/2)+d := by dsimp [d]; omega
  have hh : (3+8*H)+(5+8*Hc)=24*p := by omega
  let a := (3+8*H)*q + 1+X
  let b := (5+8*Hc)*(q+shift t n)+2+Xc
  have hstep : a+b = ((3+8*H)+(5+8*Hc))*q + (X+Xc+3) + (5+8*Hc)*(d*n) := by
    dsimp [a,b,shift,d]
    simp only [Nat.mul_add, Nat.add_mul]
    omega
  have hB : (5+8*Hc)*(d*n) = d*n + p*((2+4*Hc)*d) := by
    rw [hp]
    have he: 5+8*Hc=1+2*(2+4*Hc) := by omega
    rw [he, Nat.add_mul, Nat.one_mul]
    ac_rfl
  have ht : t*n + d*n = p*(t/2+d) := by
    calc
      t*n+d*n = (2*(t/2)+d)*n+d*n := by rw [←hd]
      _ = (2*n)*(t/2+d) := by
        rw [Nat.add_mul, Nat.mul_add]
        have hd2 : d*n+d*n = (2*n)*d := by
          calc
            d*n+d*n = (d+d)*n := by rw [Nat.add_mul]
            _ = (2*n)*d := by
              rw [show d+d=2*d by omega]
              ac_rfl
        calc
          _ = 2*(t/2)*n+(d*n+d*n) := by omega
          _ = (2*n)*(t/2)+(2*n)*d := by rw [hd2]; ac_rfl
      _ = p*(t/2+d) := by rw [hp]
  have hs : p ∣ a+b := by
    refine ⟨24*q+t/2+d+(2+4*Hc)*d, ?_⟩
    rw [hstep, hh, hX, hB]
    calc
      24*p*q + t*n + (d*n + p*((2+4*Hc)*d)) =
        24*p*q+(t*n+d*n)+p*((2+4*Hc)*d) := by omega
      _ = 24*p*q+p*(t/2+d)+p*((2+4*Hc)*d) := by rw [ht]
      _ = p*(24*q+t/2+d+(2+4*Hc)*d) := by
        simp only [Nat.mul_add]
        ac_rfl
  constructor
  · intro ha
    change p ∣ a at ha
    change p ∣ b
    exact (Nat.dvd_add_iff_right ha).mpr hs
  · intro hb
    change p ∣ b at hb
    change p ∣ a
    exact (Nat.dvd_add_iff_left hb).mpr hs

#print axioms algebraic_duality
end BB6.Agent50Cost
