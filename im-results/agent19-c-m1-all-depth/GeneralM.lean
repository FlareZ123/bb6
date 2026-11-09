import CAllDepthBlank
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19GeneralM
open BB6.Agent4Four
open BB6.Agent46

def w (a : Nat) : Nat := 2^(8*a+2)
def s (a q : Nat) : Nat := 4*w a*q+2*w a-(7*a+3)
def t (a q : Nat) : Nat := 4*w a*q+2*w a-(q+3*a+4)
def j (a q : Nat) : Nat := 4*s a q+16*a+6
def m (a : Nat) : Nat := 4*a+1
def k (a q : Nat) : Nat := bandY (8*a+2) (t a q)

private theorem w_linear_lower (a : Nat) : 8*a+8 ≤ 2*w a := by
  induction a with
  | zero => decide
  | succ a ih =>
      have he : 8*(a+1)+2=(8*a+2)+8 := by omega
      have hpow : w (a+1)=256*w a := by
        dsimp [w]
        rw [he,Nat.pow_add]
        simp only [show (2:Nat)^8=256 by decide]
        ac_rfl
      rw [hpow]
      omega

private theorem s_exact (a q : Nat) :
    s a q+7*a+3=4*w a*q+2*w a := by
  unfold s
  have h := w_linear_lower a
  have hle : 7*a+3 ≤ 4*w a*q+2*w a := by omega
  have heq := Nat.sub_add_cancel hle
  omega

private theorem t_exact (a q : Nat) :
    t a q+q+3*a+4=4*w a*q+2*w a := by
  unfold t
  have hw : 1 ≤ w a := Nat.pow_pos (by decide)
  have hq : q ≤ (4*w a)*q := by
    have hq1 : 1 ≤ 4*w a := by omega
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right q hq1
  have hl := w_linear_lower a
  have hle : q+3*a+4 ≤ 4*w a*q+2*w a := by omega
  omega

private theorem j_t_relation (a q : Nat) :
    j a q=4*t a q+4*q+10 := by
  have hs := s_exact a q
  have ht := t_exact a q
  dsimp [j]
  omega

private theorem j_source_relation (a q : Nat) :
    j a q+12*a+6=4*w a*(4*q+2) := by
  have hs := s_exact a q
  have hprod : 4*w a*(4*q+2)=4*(4*w a*q+2*w a) := by
    simp only [Nat.mul_add]
    congr 1 <;> ac_rfl
  rw [hprod]
  dsimp [j]
  omega

private theorem k_plus_two (a q : Nat) :
    k a q+2=w a*(16*t a q+44) := by
  have hw : 1≤w a := Nat.pow_pos (by decide)
  have hp : 2≤w a*(16*t a q+44) := by
    have hmult := Nat.mul_le_mul_right (16*t a q+44) hw
    omega
  dsimp [k,bandY,w]
  exact Nat.sub_add_cancel hp

private theorem power_eq (a : Nat) :
    (2:Nat)^(2*m a+2)=4*w a := by
  unfold m w
  have he : 2*(4*a+1)+2=(8*a+2)+2 := by omega
  rw [he, Nat.pow_add]
  simp only [show (2:Nat)^2=4 by decide]
  ac_rfl

private theorem algebra_core (a q : Nat) :
    w a*(16*t a q+44)+4*w a*(4*q+2)=
      4*w a*(j a q+3) := by
  have hj := j_t_relation a q
  calc
    w a*(16*t a q+44)+4*w a*(4*q+2) =
        w a*(16*t a q+44)+w a*(4*(4*q+2)) := by
          congr 1
          ac_rfl
    _ = w a*((16*t a q+44)+4*(4*q+2)) := by
      simp [Nat.mul_add, Nat.add_assoc]
    _ = w a*(4*(j a q+3)) := by
      congr 1
      omega
    _ = 4*w a*(j a q+3) := by ac_rfl

theorem general_high_stopping (a q : Nat) :
    k a q+j a q+3*m a+5=(2:Nat)^(2*m a+2)*(j a q+3) := by
  rw [power_eq]
  have hk := k_plus_two a q
  have hj := j_source_relation a q
  have hc := algebra_core a q
  dsimp [m]
  omega

theorem general_unreachable (a q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*j a q+3,k a q) := by
  have hx : 2*j a q+3=8*s a q+7+4*(8*a+2) := by
    dsimp [j]
    omega
  rw [hx]
  exact blank_excludes_all_depth_cylinders (8*a+2) (s a q) (t a q) time

#print axioms general_high_stopping
#print axioms general_unreachable
end BB6.Agent19GeneralM
