import Lean.Elab.Tactic.Omega

namespace BB6.Agent11HighThreeLate

/-- An exact original high stopping target can enter the complementary
    odd-part-three cone at depths beyond its stopping power. -/
theorem late_high_arithmetic (r j m k : Nat)
    (_hr : 2≤r) (hm : 3≤m)
    (hm4 : m%4=(2*r+1)%4)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hmod : (k+2)%2^(r+2)=3*2^r)
    (hsize : 7*2^r≤k+2) :
    ∃ u : Nat, 7≤u ∧ u%4=3 ∧ k+2=2^r*u ∧
      (2*j+3+2*k+4*r)%8=3 := by
  let R := (2:Nat)^r
  let Q := 2^(r+2)
  let S := k+2
  have hRpos : 0<R := by dsimp [R]; exact Nat.pow_pos (by decide)
  have hQ : Q=4*R := by
    dsimp [Q,R]
    rw [Nat.pow_add]
    simp only [show (2:Nat)^2=4 by decide]
    omega
  let w := S/Q
  have hSrepr : S=R*(4*w+3) := by
    have h0 : S=3*R+Q*w := by
      calc
        S=S%Q+Q*(S/Q) := (Nat.mod_add_div S Q).symm
        _=3*R+Q*w := by
          simpa only [S,Q,R] using
            congrArg (fun z : Nat => z+Q*(S/Q)) hmod
    calc
      S=3*R+Q*w := h0
      _=R*(4*w+3) := by
        rw [hQ]
        simp only [Nat.mul_add]
        ac_rfl
  have hu7 : 7≤4*w+3 := by
    have hb : R*7≤R*(4*w+3) := by
      rw [←hSrepr]
      simpa only [R,S,Nat.mul_comm] using hsize
    exact Nat.le_of_mul_le_mul_left hb (by omega)
  have hmass : (2*j+3+2*k+4*r)%8=3 := by
    have hP4 : 4 ∣ (2:Nat)^(2*m+2) := by
      simpa only [show (2:Nat)^2=4 by decide] using
        (Nat.pow_dvd_pow 2 (by omega : 2≤2*m+2))
    have hPprod4 : 4∣2^(2*m+2)*(j+3) := by
      rcases hP4 with ⟨v,hPv⟩
      refine ⟨v*(j+3),?_⟩
      rw [hPv]
      simp only [Nat.mul_assoc]
    have hPmod : (k+j+3*m+5)%4=0 := by
      rw [hstop]
      exact Nat.mod_eq_zero_of_dvd hPprod4
    omega
  refine ⟨4*w+3,hu7,?_ ,hSrepr,hmass⟩
  omega

#print axioms late_high_arithmetic
end BB6.Agent11HighThreeLate
