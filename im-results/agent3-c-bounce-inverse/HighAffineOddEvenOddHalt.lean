import AffineOddEvenOddCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A genuine higher Machine C halting family in the new four-return
    affine/odd-even-odd source-exact forbidden cone, with no time bound.
    The first included parameters are m=4,j=283 and all j=283 mod512
    with that m; for m>=4 the equation supplies the height bound. -/
theorem high_halt_affine_oeo_512_unreachable
    (j m k time : Nat)
    (hm : 4≤m)
    (hm4 : m%4=0)
    (hjm : (j+511*m)%512=279)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (2*j+3,k) := by
  let P := 2^(2*m+2)
  have hPbound : 16*(m+1)≤P := by
    have hh := halting_power_linear (m-2)
    have he : 2*(m-2)+6=2*m+2 := by omega
    have hr : 16*((m-2)+3)=16*(m+1) := by omega
    simpa only [P,he,hr] using hh
  have hP1 : 1≤P := by dsimp [P]; exact Nat.one_le_two_pow
  have hProd : P*(j+3)=P*j+3*P := by simp [Nat.mul_add]; omega
  have hPj : j≤P*j := by
    have hh := Nat.le_mul_of_pos_right j hP1
    simpa [Nat.mul_comm] using hh
  have hk20 : 20≤k := by
    change k+j+3*m+5=P*(j+3) at hgate
    rw [hProd] at hgate
    omega
  have hPdiv : 512∣P := by
    dsimp [P]
    change 2^9∣2^(2*m+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨z,hz⟩ := hPdiv
  have hmod512 : (k+j+3*m+5)%512=0 := by
    have hd : 512∣k+j+3*m+5 := by
      refine ⟨z*(j+3),?_⟩
      calc
        k+j+3*m+5=P*(j+3) := hgate
        _=(512*z)*(j+3) := by rw [hz]
        _=512*(z*(j+3)) := by ac_rfl
    exact Nat.mod_eq_zero_of_dvd hd
  have hs1 : ((2*j+3)+k)%8=5 := by omega
  have hs2 : (2*(2*j+3)+k)%512=326 := by omega
  exact affine_odd_even_odd_cone_unreachable (2*j+3) k time hk20 hs1 hs2

#print axioms high_halt_affine_oeo_512_unreachable
end BB6.Agent3
