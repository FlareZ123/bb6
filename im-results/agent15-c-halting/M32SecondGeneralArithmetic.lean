import M32SecondMassCases
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 2000000

namespace BB6.Agent15

/-- The original second halting equation gives a *general* odd-affine-depth
    normal form for every m≡3 modulo four, without fixing m mod16. -/
theorem second_m32_mass_structure (m k r j q : Nat)
    (hm : m%4=3) (hr : r+3≤m) (hqj : q≤j)
    (hX : j+3*m+3=2^(2*r+2)*(2*q+1))
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3)) :
    ∃ Q : Nat, 1≤Q ∧
      k=2^((2*r+1)+1)*(2*Q+1)-2 ∧
      (2*j+3)%4=3 ∧
      ((2*j+3)+2*k+6*m+7)%32=0 ∧
      (Q+q+1)%8=0 := by
  let P : Nat := 2^(2*r+2)
  let S : Nat := 2^(2*m-2*r-1)
  let T : Nat := S*(j+3)
  let Q : Nat := T-q-1
  have hp4 : 4 ∣ P := by
    dsimp [P]
    have h : 2^2 ∣ 2^(2*r+2) := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hjMod : (j+3*m+3)%4=0 := by
    rw [hX]
    have hpDiv : 4 ∣ 2^(2*r+2) := by simpa [P] using hp4
    apply Nat.mod_eq_zero_of_dvd
    rcases hpDiv with ⟨z,hz⟩
    refine ⟨z*(2*q+1),?_⟩
    rw [hz]
    ac_rfl
  have hjEven : (2*j+3)%4=3 := by omega
  have hpow32 : 32 ∣ 2^(2*m+2) := by
    have h : 2^5 ∣ 2^(2*m+2) := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hmul32 : 32 ∣ 2^(2*m+2)*(j+3) := by
    rcases hpow32 with ⟨z,hz⟩
    refine ⟨z*(j+3),?_⟩
    rw [hz]
    ac_rfl
  have hmod : (k+j+3*m+5)%32=0 := by
    rw [hk]
    exact Nat.mod_eq_zero_of_dvd hmul32
  have hmassZero : ((2*j+3)+2*k+6*m+7)%32=0 := by omega
  have hSdiv : 8 ∣ S := by
    dsimp [S]
    have h : 2^3 ∣ 2^(2*m-2*r-1) := Nat.pow_dvd_pow 2 (by omega)
    simpa using h
  have hTmod : T%8=0 := by
    dsimp [T]
    apply Nat.mod_eq_zero_of_dvd
    rcases hSdiv with ⟨z,hz⟩
    refine ⟨z*(j+3),?_⟩
    rw [hz]
    ac_rfl
  have hSpos : 0<S := Nat.pow_pos (by decide)
  have hTsize : j+3≤T := by
    dsimp [T]
    exact Nat.le_mul_of_pos_left (j+3) hSpos
  have hQpos : 1≤Q := by dsimp [Q]; omega
  have hQsum : 2*Q+1+2*q+1=2*T := by dsimp [Q]; omega
  have hExp : 2*m+2=(2*r+2)+(2*m-2*r) := by omega
  have hSpow : 2^(2*m-2*r)=2*S := by
    have he : 2*m-2*r=(2*m-2*r-1)+1 := by omega
    calc
      2^(2*m-2*r) = 2^((2*m-2*r-1)+1) := congrArg (fun t : Nat => 2^t) he
      _ = 2^(2*m-2*r-1)*2 := Nat.pow_succ 2 (2*m-2*r-1)
      _ = 2*S := by dsimp [S]; ac_rfl
  have hPpow : 2^(2*m+2)=P*(2*S) := by
    rw [hExp,Nat.pow_add,hSpow]
  have hPT : 2^(2*m+2)*(j+3)=P*(2*T) := by
    rw [hPpow]
    dsimp [T]
    ac_rfl
  have hE : k+2+P*(2*q+1)=P*(2*T) := by
    rw [←hPT,←hX]
    omega
  have hEq : P*(2*Q+1)+P*(2*q+1)=P*(2*T) := by
    calc
      P*(2*Q+1)+P*(2*q+1) = P*((2*Q+1)+(2*q+1)) :=
        (Nat.mul_add P (2*Q+1) (2*q+1)).symm
      _ = P*(2*T) := by rw [show (2*Q+1)+(2*q+1)=2*T by omega]
  have hK : k+2=P*(2*Q+1) := by omega
  have hkForm : k=2^((2*r+1)+1)*(2*Q+1)-2 := by
    change k=P*(2*Q+1)-2
    omega
  have hqmod : (Q+q+1)%8=0 := by dsimp [Q]; omega
  exact ⟨Q,hQpos,hkForm,hjEven,hmassZero,hqmod⟩

#print axioms second_m32_mass_structure
end BB6.Agent15
