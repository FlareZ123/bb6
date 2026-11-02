import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/-- The eight source-M32 depth classes, expressed without quotient dependencies. -/
def m32SecondClass (d q : Nat) : Prop :=
    (d%8=1 ∧ (q%8=7 ∨ q%8=4)) ∨
    (d%8=3 ∧ (q%8=5 ∨ q%8=0)) ∨
    (d%8=5 ∧ (q%8=4 ∨ q%8=3)) ∨
    (d%8=7 ∧ (q%8=1 ∨ q%8=0))

/-- The corresponding congruences on the true second stopping family. -/
def m32SecondParamClass (r q : Nat) : Prop :=
    (r%4=0 ∧ (q%8=0 ∨ q%8=3)) ∨
    (r%4=1 ∧ (q%8=2 ∨ q%8=7)) ∨
    (r%4=2 ∧ (q%8=3 ∨ q%8=4)) ∨
    (r%4=3 ∧ (q%8=6 ∨ q%8=7))

set_option maxHeartbeats 1000000

/-- Fully arithmetic conversion from a genuine second stopping equation to
    an arbitrary odd-depth M32-normalized forbidden form. -/
theorem second_m32_arithmetic (m k r j q : Nat)
    (hm : m%16=11) (hr : r+3≤m) (hqj : q≤j)
    (hX : j+3*m+3=2^(2*r+2)*(2*q+1))
    (hk : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hclass : m32SecondParamClass r q) :
    ∃ Q : Nat, 1≤Q ∧
      k=2^((2*r+1)+1)*(2*Q+1)-2 ∧
      (2*j+3)%4=3 ∧
      ((2*j+3)+2*k)%32=23 ∧ m32SecondClass (2*r+1) Q := by
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
  have hmass : ((2*j+3)+2*k)%32=23 := by omega
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
  have hclassQ : m32SecondClass (2*r+1) Q := by
    unfold m32SecondClass m32SecondParamClass at *
    rcases hclass with ⟨hr0,hq0⟩ | ⟨hr1,hq1⟩ | ⟨hr2,hq2⟩ | ⟨hr3,hq3⟩
    · rcases hq0 with h|h <;> omega
    · rcases hq1 with h|h <;> omega
    · rcases hq2 with h|h <;> omega
    · rcases hq3 with h|h <;> omega
  exact ⟨Q,hQpos,hkForm,hjEven,hmass,hclassQ⟩

/-- All odd 2-adic inverse depths occur among genuine second-branch
    stopping candidates, with arbitrarily large halting index m. -/
theorem second_m32_witness_indices (r lower : Nat) :
    ∃ m j k q : Nat, lower≤m ∧ m%16=11 ∧ r+3≤m ∧ q≤j ∧
    j+3*m+3=2^(2*r+2)*(2*q+1) ∧
    k+j+3*m+5=2^(2*m+2)*(j+3) ∧ m32SecondParamClass r q := by
  let m : Nat := 16*(r+lower)+11
  let q : Nat := 8*m+2*(r%4)
  let P : Nat := 2^(2*r+2)
  have hm : m%16=11 := by dsimp [m]; omega
  have hmlower : lower≤m := by dsimp [m]; omega
  have hr : r+3≤m := by dsimp [m]; omega
  have hqsize : m≤q := by dsimp [q]; omega
  have hclass : m32SecondParamClass r q := by
    unfold m32SecondParamClass
    dsimp [q]
    have hrest : r%4<4 := Nat.mod_lt r (by decide)
    omega
  have hP4 : 4≤P := by
    have hp : 0<2^(2*r) := Nat.pow_pos (by decide)
    have hexp : 2*r+2=(2*r)+2 := by omega
    dsimp [P]
    rw [hexp,Nat.pow_add]
    omega
  have hPbig : q+3*m+3 ≤ P*(2*q+1) := by
    have hh : 4*(2*q+1) ≤ P*(2*q+1) :=
      Nat.mul_le_mul_right (2*q+1) hP4
    omega
  let j : Nat := P*(2*q+1)-(3*m+3)
  have hjq : q≤j := by dsimp [j]; omega
  have hjm : m≤j := by omega
  have hX : j+3*m+3=2^(2*r+2)*(2*q+1) := by
    change j+3*m+3=P*(2*q+1)
    dsimp [j]
    omega
  let H : Nat := 2^(2*m+2)*(j+3)
  have hp8 : 8≤2^(2*m+2) := by
    have he : 2*m+2=3+(2*m-1) := by omega
    rw [he,Nat.pow_add]
    have hpos : 0<2^(2*m-1) := Nat.pow_pos (by decide)
    omega
  have hH : j+3*m+5≤H := by
    have hmul : 8*(j+3) ≤ 2^(2*m+2)*(j+3) :=
      Nat.mul_le_mul_right (j+3) hp8
    dsimp [H]
    omega
  let k : Nat := H-(j+3*m+5)
  have hk : k+j+3*m+5=2^(2*m+2)*(j+3) := by dsimp [k,H]; omega
  exact ⟨m,j,k,q,hmlower,hm,hr,hjq,hX,hk,hclass⟩

#print axioms second_m32_witness_indices
#print axioms second_m32_arithmetic
end BB6.Agent15
