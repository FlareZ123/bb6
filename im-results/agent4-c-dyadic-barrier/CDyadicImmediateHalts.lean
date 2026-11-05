import UnifiedGateway
import Lean.Elab.Tactic.Omega

namespace BB6CDyadicBarrier

/-- Nonnegative geometric series of powers of four. -/
def geom : Nat → Nat
  | 0 => 0
  | n+1 => 4*geom n+1

private theorem geom_id (n : Nat) : 3*geom n+1 = 4^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      change 3*(4*geom n+1)+1=4^(n+1)
      rw [Nat.pow_succ]
      omega

/-- Parameters forcing the linear correction onto a full power of four. -/
def height (e C : Nat) : Nat :=
  C*geom e + (C+e+1)*4^e

private theorem height_cost (e C : Nat) :
    3*height e C+C = (4*C+3*e+3)*4^e := by
  unfold height
  calc
    3*(C*geom e+(C+e+1)*4^e)+C =
      C*(3*geom e+1)+3*(C+e+1)*4^e := by
        simp only [Nat.mul_add, Nat.add_mul]
        ac_rfl
    _ = C*4^e+3*(C+e+1)*4^e := by rw [geom_id]
    _ = (C+3*(C+e+1))*4^e := by rw [Nat.add_mul]
    _ = (4*C+3*e+3)*4^e := by
      have hc : C+3*(C+e+1) = 4*C+3*e+3 := by omega
      rw [hc]

private theorem height_large (e C : Nat) : C+e+1 ≤ height e C := by
  unfold height
  have hp : 0<4^e := Nat.pow_pos (by decide)
  have hb : C+e+1 ≤ (C+e+1)*4^e := by
    calc
      C+e+1=(C+e+1)*1 := by omega
      _ ≤ (C+e+1)*4^e := Nat.mul_le_mul_left _ (by omega)
  omega

private theorem power_big (m : Nat) : 4*(m+1) ≤ 4^(m+1) := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [show m+1+1=(m+1)+1 by omega, Nat.pow_succ]
      omega

private theorem exponential_bound (u C m : Nat) (h : C≤m) :
    3*m+C ≤ 4^(m+1)*(u+2) := by
  have hp:=power_big m
  have ht : 4^(m+1) ≤ 4^(m+1)*(u+2) := by
    calc
      4^(m+1)=4^(m+1)*1 := by omega
      _ ≤ 4^(m+1)*(u+2) := Nat.mul_le_mul_left _ (by omega)
  omega

/-- The complete, parameterized immediate-stop right counter. -/
def stopRight (e u w : Nat) : Nat :=
  let C := u+w+4
  let m := height e C
  4^(m+1)*(u+2) - (u+3*m+4)

private theorem stopRight_identity (e u w : Nat) :
    stopRight e u w + u+3*height e (u+w+4)+4 =
      4^(height e (u+w+4)+1)*(u+2) := by
  dsimp [stopRight]
  have hm : u+w+4 ≤ height e (u+w+4) := by
    have h:=height_large e (u+w+4)
    omega
  have hh := exponential_bound u (u+w+4) (height e (u+w+4)) hm
  omega

private theorem stopRight_ge (e u w : Nat) : w≤stopRight e u w := by
  have hm : u+w+4 ≤ height e (u+w+4) := by
    have h:=height_large e (u+w+4)
    omega
  have hh := exponential_bound u (u+w+4) (height e (u+w+4)) hm
  have he := stopRight_identity e u w
  omega

private theorem power_four_multiple (e : Nat) : 2^e ∣ 4^e := by
  have h : 4^e=2^e*2^e := by
    calc
      4^e=(2*2)^e := by rfl
      _=2^e*2^e := by rw [Nat.mul_pow]
  rw [h]
  exact Nat.dvd_mul_right _ _

private theorem stopRight_mod (e u w : Nat) :
    stopRight e u w % (2^e) = w % (2^e) := by
  let C:=u+w+4
  let m:=height e C
  have hm : e≤m := by
    have h:=height_large e C
    omega
  have hp : 4^e ∣ 4^(m+1) := Nat.pow_dvd_pow 4 (by omega)
  have hfirst : 2^e ∣ 4^(m+1)*(u+2) := by
    have hbase : 2^e ∣ 4^e := power_four_multiple e
    obtain ⟨j,hj⟩ := hp
    refine Nat.dvd_trans hbase ?_
    refine ⟨j*(u+2), ?_⟩
    rw [hj]
    ac_rfl
  have hsecond : 2^e ∣ 3*m+C := by
    have hi:=height_cost e C
    have h4 : 4^e ∣ 3*m+C := by
      rw [hi]
      exact Nat.dvd_mul_left _ _
    exact Nat.dvd_trans (power_four_multiple e) h4
  have he : stopRight e u w - w = 4^(m+1)*(u+2) - (3*m+C) := by
    have hid:=stopRight_identity e u w
    have hge:=stopRight_ge e u w
    dsimp [m,C] at *
    omega
  have hd : 2^e ∣ stopRight e u w-w := by
    rw [he]
    exact Nat.dvd_sub hfirst hsecond
  have hge := stopRight_ge e u w
  have heq : stopRight e u w = w+(stopRight e u w-w) := by omega
  rw [heq,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd]
  simp

/-- Every pair (odd first counter, right residue) modulo any 2-power
    contains an *immediate* source halting input for the Machine C section. -/
theorem every_odd_dyadic_class_has_immediate_halt (e u w : Nat) :
    ∃ K, K % (2^e)=w % (2^e) ∧
      BB6.Agent46.secNext (2*u+1,K)=none := by
  let m:=height e (u+w+4)
  let K:=stopRight e u w
  have he : K+u+3*m+4=4^(m+1)*(u+2) := by
    exact stopRight_identity e u w
  have heq : (2*u+1)+2*K+6*m+7=4^(m+1)*((2*u+1)+3) := by
    have hscale : 4^(m+1)*(2*u+1+3)=2*(4^(m+1)*(u+2)) := by
      rw [show 2*u+1+3=2*(u+2) by omega]
      ac_rfl
    rw [hscale]
    omega
  have hhalt := (BB6.Agent1Unified.source_section_halts_iff_one_equation (2*u+1) K).mpr
    (Or.inr ⟨by omega,by omega,m,heq⟩)
  exact ⟨K,stopRight_mod e u w,hhalt⟩

/-- Genuine blank section (5,1) is indistinguishable modulo each 2-power
    from a synthetic state at which the source section halts immediately. -/
theorem blank_class_has_synthetic_halt (e : Nat) :
    ∃ K, K % (2^e)=1 % (2^e) ∧ BB6.Agent46.secNext (5,K)=none := by
  simpa using every_odd_dyadic_class_has_immediate_halt e 2 1

#print axioms every_odd_dyadic_class_has_immediate_halt
#print axioms blank_class_has_synthetic_halt
end BB6CDyadicBarrier
