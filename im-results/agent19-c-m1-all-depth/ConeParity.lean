import CAllDepthBlank
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19ConeParity
open BB6.Agent4Four

/-- The strict-image cone of Agent 4 can intersect the genuine Machine C
    high-stopping surface only at positive odd stopping indices. Its
    image depth parity is forced exactly by the stopping index mod four. -/
theorem high_stopping_cone_parity (m r s t j k : Nat)
    (hr : 2≤r)
    (hj : j=4*s+2*r+2)
    (hk : k=bandY r t)
    (hstop : k+j+3*m+5=(2:Nat)^(2*m+2)*(j+3)) :
    m%2=1 ∧
    (m%4=1 → r%2=0) ∧
    (m%4=3 → r%2=1) := by
  have hpow4 : 4 ∣ (2:Nat)^(2*m+2) := by
    have h := Nat.pow_dvd_pow 2 (by omega : 2≤2*m+2)
    simpa only [show (2:Nat)^2=4 by decide] using h
  have hpowr4 : 4 ∣ (2:Nat)^r := by
    have h := Nat.pow_dvd_pow 2 hr
    simpa only [show (2:Nat)^2=4 by decide] using h
  have hPmod : (k+j+3*m+5)%4=0 := by
    rw [hstop]
    rcases hpow4 with ⟨u,hu⟩
    apply Nat.mod_eq_zero_of_dvd
    refine ⟨u*(j+3),?_⟩
    rw [hu]
    ac_rfl
  have hrprod : 4 ∣ (2:Nat)^r*(16*t+44) := by
    rcases hpowr4 with ⟨u,hu⟩
    refine ⟨u*(16*t+44),?_⟩
    rw [hu]
    ac_rfl
  have hpos : 2 ≤ (2:Nat)^r*(16*t+44) := by
    have hp : 1≤(2:Nat)^r := Nat.pow_pos (by decide)
    have hb := Nat.mul_le_mul_right (16*t+44) hp
    omega
  have hPlus : k+2=(2:Nat)^r*(16*t+44) := by
    rw [hk]
    dsimp [bandY]
    exact Nat.sub_add_cancel hpos
  have hkmod : (k+2)%4=0 := by
    rw [hPlus]
    exact Nat.mod_eq_zero_of_dvd hrprod
  have hjmod : (j-2*r-2)%4=0 := by
    rw [hj]
    have h : 2*r+2 ≤ 4*s+2*r+2 := by omega
    omega
  omega

#print axioms high_stopping_cone_parity
end BB6.Agent19ConeParity
