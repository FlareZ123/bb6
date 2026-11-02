import DeepFamily
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11

private theorem modular_lift_generic (P W t U : Nat)
    (hU : 0<U)
    (heq : U+2*P*(4*t+1)=2*P*(84*W)) :
    ∃ q, U=2*P*(4*q+3) := by
  have hsmall : 4*t+1 < 84*W := by
    by_cases h : 4*t+1 < 84*W
    · exact h
    · have hle : 84*W ≤ 4*t+1 := by omega
      have hh := Nat.mul_le_mul_left (2*P) hle
      omega
  have hq : t+1 ≤ 21*W := by omega
  let q : Nat := 21*W-t-1
  have hfactor : 4*q+3+(4*t+1)=84*W := by
    dsimp [q]
    omega
  have heq2 : 2*P*(4*q+3)+2*P*(4*t+1)=2*P*(84*W) := by
    have hh := congrArg (fun x : Nat => (2*P)*x) hfactor
    simpa only [Nat.mul_add] using hh
  refine ⟨q,?_⟩
  omega

private theorem bridge (P W u s t : Nat)
    (hP : 0<P)
    (hu : u+6*s+1=8*(P*W))
    (hs : 63*s+11=P*(4*t+1)) :
    ∃ q, 21*u-1 = (2*P)*(4*q+3) := by
  have hu0 : 0<u := by
    have hW : 0<W := by
      by_cases h : W=0
      · simp [h] at hu
      · omega
    have hh : 0<P*W := Nat.mul_pos hP hW
    omega
  have hS2 : (2*P)*(4*t+1) = 2*(63*s+11) := by
    calc
      (2*P)*(4*t+1) = 2*(P*(4*t+1)) := by ac_rfl
      _ = 2*(63*s+11) := by rw [←hs]
  have hR : (2*P)*(84*W) = 168*(P*W) := by
    calc
      (2*P)*(84*W) = (2*84)*(P*W) := by ac_rfl
      _ = 168*(P*W) := by rfl
  have hU : (21*u-1)+(2*P)*(4*t+1)=(2*P)*(84*W) := by
    rw [hS2,hR]
    omega
  exact modular_lift_generic P W t (21*u-1) (by omega) hU

private theorem first_halt_arithmetic_lift
    (m k r s t W : Nat)
    (hm : m=64*s+8)
    (hs : 63*s+11=2^(2*r)*(4*t+1))
    (hpow : 2^(2*m+3)=256*2^(2*r)*W)
    (hk : k+3*m+4=2^(2*m+3)) :
    ∃ u q, k=32*u+4 ∧ 21*u-1=2^(2*r+1)*(4*q+3) := by
  let P : Nat := 2^(2*r)
  have hP : 0<P := Nat.pow_pos (by decide)
  have hpow' : k+3*m+4=256*(P*W) := by
    calc
      k+3*m+4=2^(2*m+3) := hk
      _ = 256*2^(2*r)*W := hpow
      _ = 256*(P*W) := by dsimp [P]; ac_rfl
  have hkmod : k%32=4 := by omega
  let u : Nat := (k-4)/32
  have hku : k=32*u+4 := by dsimp [u]; omega
  have hu : u+6*s+1=8*(P*W) := by
    rw [hm,hku] at hpow'
    omega
  have hs' : 63*s+11=P*(4*t+1) := by exact hs
  obtain ⟨q,hq⟩ := bridge P W u s t hP hu hs'
  have he : 2^(2*r+1)=2*P := by
    dsimp [P]
    rw [Nat.pow_succ]
    ac_rfl
  refine ⟨u,q,hku,?_⟩
  rw [he]
  exact hq

private theorem two_power_factor (m r : Nat) (h : r+3 ≤ m) :
    ∃ W, 2^(2*m+3)=256*2^(2*r)*W := by
  let d : Nat := 2*m-2*r-5
  have he : 2*m+3=(2*r+8)+d := by dsimp [d]; omega
  refine ⟨2^d,?_⟩
  rw [he,Nat.pow_add]
  have h256 : 2^(2*r+8)=2^(2*r)*256 := by
    rw [Nat.pow_add]
  rw [h256]
  ac_rfl

/-- A uniform, unbounded-depth obstruction for the authentic Machine C
    first-family stopping locus. The Diophantine hypothesis is an exact
    congruence/lifting condition on the stopping index m=64*s+8. -/
theorem uniform_first_halt_depth (m k r s t : Nat)
    (hm : m=64*s+8)
    (hs : 63*s+11=2^(2*r)*(4*t+1))
    (hr : r+3≤m)
    (hk : k+3*m+4=2^(2*m+3)) : ¬ BB6.Agent3.CReach 1 k := by
  obtain ⟨W,hpow⟩ := two_power_factor m r hr
  obtain ⟨u,q,hku,heq⟩ :=
    first_halt_arithmetic_lift m k r s t W hm hs hpow hk
  intro hreach
  rw [hku] at hreach
  exact deep_low_gate_diophantine r q u heq hreach

#print axioms uniform_first_halt_depth
end BB6.Agent11
