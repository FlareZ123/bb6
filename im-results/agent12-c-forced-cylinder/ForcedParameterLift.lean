import ForcedCylinder
import Lean.Elab.Tactic.Omega

namespace BB6.Agent12ForcedCylinder
open BB6.Agent3

def highX (j : Nat) : Nat := 2*j+3
def highY (j m : Nat) : Nat := 2^(2*m+2)*(j+3)-(j+3*m+5)
def lowY (m : Nat) : Nat := 2^(2*m+3)-(3*m+4)

def p4 (m : Nat) : Nat := 4^(m+1)
private theorem p4_eq (m : Nat) : 2^(2*m+2)=p4 m := by
  unfold p4
  rw [show 2*m+2=2*(m+1) by omega, Nat.pow_mul]
private theorem p4_succ (m : Nat) : p4 (m+1)=4*p4 m := by
  unfold p4
  rw [Nat.pow_succ, Nat.mul_comm]
private theorem p4_lower (m : Nat) : m+2≤p4 m := by
  induction m with
  | zero => decide
  | succ m ih => rw [p4_succ]; omega
private theorem p4_growth (m n : Nat) : p4 m+n≤p4 (m+n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m+(n+1)=m+n+1 by omega,p4_succ]
    have hp := p4_lower (m+n)
    omega
private theorem p4_mono {m m' : Nat} (h : m≤m') : p4 m+(m'-m)≤p4 m' := by
  have h0 := p4_growth m (m'-m)
  rw [Nat.add_sub_of_le h] at h0
  exact h0
private theorem high_add (j m : Nat) : highY j m+(j+3*m+5)=p4 m*(j+3) := by
  unfold highY
  rw [p4_eq]
  have hp := p4_lower m
  have h1 : j≤p4 m*j := by
    simpa using Nat.mul_le_mul_right j (show 1≤p4 m by omega)
  rw [Nat.mul_add]
  omega
private theorem highY_linear (j m : Nat) :
    highY j m = (p4 m-1)*j + 3*(p4 m-m-2)+1 := by
  have hp := p4_lower m
  have h := high_add j m
  rw [Nat.mul_add] at h
  have hj : (p4 m-1)*j = p4 m*j-j := by
    rw [Nat.mul_sub_right_distrib, Nat.one_mul]
  have h1 : j≤p4 m*j := by
    simpa using Nat.mul_le_mul_right j (show 1≤p4 m by omega)
  rw [hj]
  omega
private theorem highY_mono {j j' m m' : Nat} (hj : j≤j') (hm : m≤m') :
    highY j m≤highY j' m' := by
  rw [highY_linear, highY_linear]
  have hp := p4_mono hm
  have h0 : p4 m-1≤p4 m'-1 := by omega
  have h1 := Nat.mul_le_mul_right j h0
  have h2 := Nat.mul_le_mul_left (p4 m'-1) hj
  omega
private theorem highY_j_shift (j m B u : Nat) :
    highY (j+B*u) m=highY j m+B*((p4 m-1)*u) := by
  rw [highY_linear,highY_linear,Nat.mul_add,Nat.mul_left_comm (p4 m-1) B]
  omega
private theorem highX_j_shift (j B u : Nat) : highX (j+B*u)=highX j+B*(2*u) := by
  unfold highX
  rw [Nat.mul_add,Nat.mul_left_comm 2 B]
  omega

/-- For every fixed high stopping depth m, a rejected j produces an
    entire arithmetic progression of rejected stopping parameters. -/
theorem high_fixed_m_lift (j m : Nat) (h : fullForcedExcluded (highX j) (highY j m)=true) (u : Nat) :
    let B := scale (precision (highX j) (highY j m))
    fullForcedExcluded (highX (j+B*u)) (highY (j+B*u) m)=true := by
  dsimp only
  rw [highX_j_shift,highY_j_shift]
  exact fullForcedExcluded_lift _ _ h (2*u) ((p4 m-1)*u)

private theorem scale_eq_pow (d : Nat) : scale d=2^(d+4) := by
  unfold scale
  rw [Nat.pow_add, Nat.mul_comm]
private theorem scale_dvd_p4 (d m : Nat) (h : d+4≤2*m+2) : scale d∣p4 m := by
  rw [scale_eq_pow, ← p4_eq]
  exact Nat.pow_dvd_pow 2 h

private theorem highY_dvd_shift (j m B u v : Nat) (hB : B∣p4 m) :
    B∣highY (j+B*u) (m+B*v)-highY j m := by
  let J := j+B*u
  let M := m+B*v
  have hm : m≤M := by dsimp [M]; omega
  have hj : j≤J := by dsimp [J]; omega
  have hmono := highY_mono hj hm
  have hpow : p4 m∣p4 M := by unfold p4; exact Nat.pow_dvd_pow 4 (by omega)
  have hA : B∣p4 M*(J+3) := Nat.dvd_trans (Nat.dvd_trans hB hpow) (Nat.dvd_mul_right _ _)
  have hC : B∣p4 m*(j+3) := Nat.dvd_trans hB (Nat.dvd_mul_right _ _)
  have hdiff := Nat.dvd_sub hA hC
  have h0 := high_add j m
  have h1 := high_add J M
  have hL : (J+3*M+5)-(j+3*m+5)=B*(u+3*v) := by
    dsimp [J,M]
    simp only [Nat.mul_add,Nat.mul_left_comm B 3]
    omega
  have hle : j+3*m+5≤J+3*M+5 := by omega
  have hEq : highY J M-highY j m = (p4 M*(J+3)-p4 m*(j+3))-((J+3*M+5)-(j+3*m+5)) := by omega
  change B∣highY J M-highY j m
  rw [hEq,hL]
  exact Nat.dvd_sub hdiff (Nat.dvd_mul_right _ _)

/-- When the base exponential term has reached the required two-adic
    precision, both high stopping parameters can be lifted simultaneously. -/
theorem high_rectangle_lift (j m : Nat)
    (h : fullForcedExcluded (highX j) (highY j m)=true)
    (hs : precision (highX j) (highY j m)+4≤2*m+2) (u v : Nat) :
    let B := scale (precision (highX j) (highY j m))
    fullForcedExcluded (highX (j+B*u)) (highY (j+B*u) (m+B*v))=true := by
  let B := scale (precision (highX j) (highY j m))
  change fullForcedExcluded (highX (j+B*u)) (highY (j+B*u) (m+B*v))=true
  have hB : B∣p4 m := scale_dvd_p4 _ _ hs
  obtain ⟨w,hw⟩ := highY_dvd_shift j m B u v hB
  have hmono : highY j m≤highY (j+B*u) (m+B*v) := highY_mono (by omega) (by omega)
  have hY : highY (j+B*u) (m+B*v) = highY j m+B*w := by omega
  rw [highX_j_shift,hY]
  exact fullForcedExcluded_lift _ _ h (2*u) w

private theorem low_add (m : Nat) : lowY m+(3*m+4)=2*p4 m := by
  unfold lowY
  rw [show 2*m+3=(2*m+2)+1 by omega, Nat.pow_succ,p4_eq, Nat.mul_comm (p4 m) 2]
  have hp := p4_lower m
  -- p4 grows by at least 3 per increment, so 2*p4 dominates 3*m+4.
  have hstrong : 2*m+4≤p4 m := by
    clear hp
    induction m with
    | zero => decide
    | succ m ih => rw [p4_succ]; omega
  omega
private theorem lowY_mono {m m' : Nat} (hm : m≤m') : lowY m≤lowY m' := by
  have hstrong : p4 m+2*(m'-m)≤p4 m' := by
    have aux : ∀ n, p4 m+2*n≤p4 (m+n) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [show m+(n+1)=m+n+1 by omega,p4_succ]
        have hp := p4_lower (m+n)
        omega
    have h := aux (m'-m)
    rw [Nat.add_sub_of_le hm] at h
    exact h
  have h0 := low_add m
  have h1 := low_add m'
  omega

/-- Saturated low stopping parameters likewise lift with the same
    arithmetic cylinder precision. -/
theorem low_lift (m : Nat) (h : fullForcedExcluded 1 (lowY m)=true)
    (hs : precision 1 (lowY m)+4≤2*m+3) (v : Nat) :
    let B := scale (precision 1 (lowY m))
    fullForcedExcluded 1 (lowY (m+B*v))=true := by
  let B := scale (precision 1 (lowY m))
  let M := m+B*v
  change fullForcedExcluded 1 (lowY M)=true
  have hm : m≤M := by dsimp [M]; omega
  have hB : B∣2*p4 m := by
    dsimp [B]
    rw [scale_eq_pow, ← p4_eq, Nat.mul_comm 2, ← Nat.pow_succ]
    exact Nat.pow_dvd_pow 2 (by omega)
  have hp : 2*p4 m∣2*p4 M := by
    obtain ⟨w,hw⟩ := Nat.pow_dvd_pow 4 (show m+1≤M+1 by omega)
    refine ⟨w,?_⟩
    change 2*4^(M+1)=2*4^(m+1)*w
    rw [hw,Nat.mul_assoc]
  have hD := Nat.dvd_sub (Nat.dvd_trans hB hp) hB
  have h0 := low_add m
  have h1 := low_add M
  have hmono := lowY_mono hm
  have hL : (3*M+4)-(3*m+4)=B*(3*v) := by
    dsimp [M]
    rw [Nat.mul_left_comm B 3]
    omega
  have hEq : lowY M-lowY m=(2*p4 M-2*p4 m)-((3*M+4)-(3*m+4)) := by omega
  have hD2 : B∣lowY M-lowY m := by
    rw [hEq,hL]
    exact Nat.dvd_sub hD (Nat.dvd_mul_right _ _)
  obtain ⟨w,hw⟩ := hD2
  have hy : lowY M=lowY m+B*w := by omega
  rw [hy]
  simpa using fullForcedExcluded_lift 1 (lowY m) h 0 w

#print axioms high_fixed_m_lift
#print axioms high_rectangle_lift
#print axioms low_lift
end BB6.Agent12ForcedCylinder
