import CAllDepthBlank
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19GeneralM3
open BB6.Agent4Four
open BB6.Agent46

def w (a : Nat) : Nat := 2^(8*a+5)
def m (a : Nat) : Nat := 4*a+3
def r (a : Nat) : Nat := 8*a+5
def s (a q : Nat) : Nat := w a*(4*q+3)-(7*a+6)
def t (a q : Nat) : Nat := 2*w a*(4*q+3)-(q+6*a+8)
def j (a q : Nat) : Nat := 4*s a q+4*m a
def k (a q : Nat) : Nat := bandY (r a) (t a q)

private theorem w_lower (a : Nat) : 8*a+12 ≤ w a := by
  induction a with
  | zero => decide
  | succ a ih =>
    have he : 8*(a+1)+5=(8*a+5)+8 := by omega
    have hpow : w (a+1)=256*w a := by
      dsimp [w]
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^8=256 by decide]
      ac_rfl
    rw [hpow]
    omega

private theorem s_exact (a q : Nat) :
    s a q+7*a+6=w a*(4*q+3) := by
  dsimp [s]
  have hw := w_lower a
  have hp : 7*a+6 ≤ w a*(4*q+3) := by
    have hc : w a ≤ w a*(4*q+3) := by
      have h3 : 1≤4*q+3 := by omega
      have h := Nat.mul_le_mul_left (w a) h3
      simpa only [Nat.mul_one] using h
    omega
  omega

private theorem t_exact (a q : Nat) :
    t a q+q+6*a+8=2*w a*(4*q+3) := by
  dsimp [t]
  have hw := w_lower a
  have hp : q+6*a+8 ≤ 2*w a*(4*q+3) := by
    have hq : q ≤ (8*w a)*q := by
      have hcoe : 1 ≤ 8*w a := by omega
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right q hcoe
    have he : 2*w a*(4*q+3)=(8*w a)*q+6*w a := by
      simp only [Nat.mul_add]
      ac_rfl
    rw [he]
    omega
  simpa only [Nat.add_assoc] using Nat.sub_add_cancel hp

private theorem j_closed (a q : Nat) :
    j a q+12*a+12=4*w a*(4*q+3) := by
  have hs := s_exact a q
  dsimp [j,m]
  have hprod : 4*(w a*(4*q+3))=4*w a*(4*q+3) := by ac_rfl
  omega

private theorem t_closed (a q : Nat) :
    16*t a q+44+4*(4*q+3)=8*(j a q+3) := by
  have ht := t_exact a q
  have hj := j_closed a q
  have hmul : 16*(2*w a*(4*q+3))=8*(4*w a*(4*q+3)) := by
    calc
      16*(2*w a*(4*q+3)) = (16*2)*(w a*(4*q+3)) := by ac_rfl
      _ = (8*4)*(w a*(4*q+3)) := by
        simp only [show (16:Nat)*2=8*4 by decide]
      _ = 8*(4*w a*(4*q+3)) := by ac_rfl
  have htm := congrArg (fun z : Nat => 16*z) ht
  have hjm := congrArg (fun z : Nat => 8*z) hj
  rw [hmul] at htm
  omega

private theorem k_plus_two (a q : Nat) :
    k a q+2=w a*(16*t a q+44) := by
  have hw := w_lower a
  have hp : 2≤w a*(16*t a q+44) := by
    have hm : w a ≤ w a*(16*t a q+44) := by
      have hcoe : 1≤16*t a q+44 := by omega
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (w a) hcoe
    omega
  dsimp [k,bandY,r,w]
  exact Nat.sub_add_cancel hp

private theorem power_eq (a : Nat) :
    (2:Nat)^(2*m a+2)=8*w a := by
  unfold m w
  have he : 2*(4*a+3)+2=(8*a+5)+3 := by omega
  rw [he,Nat.pow_add]
  simp only [show (2:Nat)^3=8 by decide]
  ac_rfl

private theorem algebra_core (a q : Nat) :
    w a*(16*t a q+44)+4*w a*(4*q+3)=8*w a*(j a q+3) := by
  have ht := t_closed a q
  calc
    w a*(16*t a q+44)+4*w a*(4*q+3) =
        w a*(16*t a q+44)+w a*(4*(4*q+3)) := by ac_rfl
    _ = w a*((16*t a q+44)+4*(4*q+3)) := by
      simp only [Nat.mul_add]
    _ = w a*(8*(j a q+3)) := by rw [ht]
    _ = 8*w a*(j a q+3) := by ac_rfl

theorem general_high_stopping (a q : Nat) :
    k a q+j a q+3*m a+5=(2:Nat)^(2*m a+2)*(j a q+3) := by
  rw [power_eq]
  have hk := k_plus_two a q
  have hj := j_closed a q
  have hc := algebra_core a q
  dsimp [m]
  omega

theorem general_unreachable (a q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j a q+3,k a q) := by
  have hx : 2*j a q+3=8*s a q+7+4*(r a) := by
    dsimp [j,r,m]
    omega
  rw [hx]
  exact blank_excludes_all_depth_cylinders (r a) (s a q) (t a q) time

private theorem dyadic_center (a q : Nat) :
    j a q+3*m a+3=4*w a*(4*q+3) := by
  have hj := j_closed a q
  dsimp [m]
  omega

private theorem center_power (a : Nat) :
    4*w a = (2:Nat)^(2*m a+1) := by
  unfold w m
  calc
    4*(2:Nat)^(8*a+5) = (2:Nat)^(8*a+5)*(2:Nat)^2 := by
      simp only [show (2:Nat)^2=4 by decide]
      ac_rfl
    _ = (2:Nat)^((8*a+5)+2) := (Nat.pow_add 2 (8*a+5) 2).symm
    _ = (2:Nat)^(2*(4*a+3)+1) := by
      congr 1
      omega

theorem general_dyadic_not_excluded (a q n : Nat) :
    ¬ (n+4 ≤ 2*m a+2 ∧
       (j a q+3*m a+3)%2^(n+4)=2^(n+2) ∧
       (2*j a q+3)%8=(if n%2=0 then 7 else 3)) := by
  rintro ⟨hn,hres,_⟩
  have hpowbound : n+3 ≤ 2*m a+1 := by omega
  have hdiv : (2:Nat)^(n+3) ∣ (2:Nat)^(2*m a+1) :=
    Nat.pow_dvd_pow 2 hpowbound
  have hd : (2:Nat)^(n+3) ∣ j a q+3*m a+3 := by
    rw [dyadic_center, center_power]
    rcases hdiv with ⟨z,hz⟩
    refine ⟨z*(4*q+3),?_⟩
    rw [hz]
    ac_rfl
  have hzero : (j a q+3*m a+3)%2^(n+3)=0 :=
    Nat.mod_eq_zero_of_dvd hd
  have hdivmod : (2:Nat)^(n+3) ∣ (2:Nat)^(n+4) :=
    Nat.pow_dvd_pow 2 (by omega)
  have hmodmod := congrArg (fun z : Nat => z % 2^(n+3)) hres
  rw [Nat.mod_mod_of_dvd _ hdivmod,hzero] at hmodmod
  have hpositive : 0 < (2:Nat)^(n+2) := Nat.pow_pos (by decide)
  have he : (2:Nat)^(n+3) = 2*(2:Nat)^(n+2) := by
    rw [show n+3=(n+2)+1 by omega,Nat.pow_succ]
    omega
  have hsmall : (2:Nat)^(n+2) < (2:Nat)^(n+3) := by omega
  have hsmallmod : (2:Nat)^(n+2) % 2^(n+3)=(2:Nat)^(n+2) :=
    Nat.mod_eq_of_lt hsmall
  rw [hsmallmod] at hmodmod
  omega

#print axioms general_dyadic_not_excluded
#print axioms general_high_stopping
#print axioms general_unreachable
end BB6.Agent19GeneralM3
