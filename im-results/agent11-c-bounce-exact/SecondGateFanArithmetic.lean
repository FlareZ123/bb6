import Lean.Elab.Tactic.Omega

namespace FanArithmetic

def m (s t : Nat) := s+t+1
def b (s t : Nat) := 3*(m s t)+4
def a (s t : Nat) := 4^t*b s t
def d (s t : Nat) := 4^(m s t+1)*b s t
def p (s t : Nat) := 4*a s t-3
def q (s t : Nat) := d s t - (2*a s t+3*m s t+7+3*s)
def x (s t : Nat) := 6*m s t+5
def y (s t : Nat) := d s t-(6*m s t+6)

theorem d_factor (s t : Nat) : d s t=16*4^s*a s t := by
  unfold d a m
  have he : s+t+1+1=(s+2)+t := by omega
  rw [he, Nat.pow_add]
  have h16 : 4^(s+2)=16*4^s := by
    rw [show s+2=2+s by omega, Nat.pow_add]
  rw [h16]
  simp [Nat.mul_assoc]

theorem a_ge_b (s t : Nat) : b s t≤a s t := by
  unfold a
  simpa using Nat.mul_le_mul_right (b s t) (Nat.one_le_pow t 4 (by decide))

theorem d_ge (s t : Nat) : 16*a s t≤d s t := by
  rw [d_factor]
  have hp : 1≤4^s:=Nat.one_le_pow s 4 (by decide)
  have ha : a s t≤4^s*a s t := by simpa using Nat.mul_le_mul_right (a s t) hp
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 16 ha

theorem bounds (s t : Nat) :
  6*m s t+6≤d s t ∧
  2*a s t+3*m s t+7+3*s≤d s t ∧
  4≤q s t ∧ 2*q s t>p s t ∧ 2≤p s t := by
  have hA:=a_ge_b s t
  have hD:=d_ge s t
  have hM : s+1≤m s t := by unfold m;omega
  have hB : b s t=3*m s t+4 := rfl
  have hlow : 7≤b s t := by omega
  have hs : 3*m s t+7+3*s≤2*b s t := by omega
  have hupper : 2*a s t+3*m s t+7+3*s≤4*a s t := by omega
  have hqq : q s t+(2*a s t+3*m s t+7+3*s)=d s t := by
    unfold q
    exact Nat.sub_add_cancel (by omega)
  have hpp : p s t+3=4*a s t := by
    unfold p
    omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

theorem y_eq (s t:Nat) : y s t+6*m s t+6=d s t := by
  unfold y
  exact Nat.sub_add_cancel (bounds s t).1

theorem target_sum (s t:Nat) : x s t +y s t+1=d s t := by
  have hh:=y_eq s t
  unfold x
  omega

theorem source_cost (s t:Nat) :
 (2*q s t-p s t+3) + (2*(p s t-1)+8) + 3*(2*s+1) = x s t+2*y s t+2 := by
 have hb:=bounds s t
 have hq: q s t+(2*a s t+3*m s t+7+3*s)=d s t := by
   unfold q
   exact Nat.sub_add_cancel hb.2.1
 have hA:=a_ge_b s t
 have hB: b s t=3*m s t+4 := rfl
 have hp:p s t+3=4*a s t := by unfold p;omega
 have hy:=y_eq s t
 have hsub : (2*q s t-p s t+3)+p s t =2*q s t+3 := by omega
 have hsub2 : p s t-1+1=p s t := by omega
 unfold x
 omega

theorem power_two (s:Nat) : 2^(2*s+1)=2*4^s := by
  rw [show 2*s+1=1+(2*s) by omega,Nat.pow_add,Nat.pow_mul,show 2^2=4 by decide]

theorem source_sum (s t:Nat) :
  2^(2*s+1)*(2*(p s t-1)+8)=x s t+y s t+1 := by
  rw [target_sum,d_factor,power_two]
  have hp:= (bounds s t).2.2.2.2
  have hA:=a_ge_b s t
  have hB : b s t=3*m s t+4 := rfl
  have hp2 : p s t+3=4*a s t := by unfold p; omega
  have hsub : p s t-1+1=p s t := by omega
  have hbase : 2*(p s t-1)+8=8*a s t := by omega
  rw [hbase]
  calc
    (2*4^s)*(8*a s t) = (2*8)*(4^s*a s t) := by ac_rfl
    _ = 16*4^s*a s t := by simp [Nat.mul_assoc]

theorem target_halt_eq (s t:Nat) :
  y s t + (3*m s t+1) + 3*(m s t)+5 = 2^(2*(m s t)+2)*((3*m s t+1)+3) := by
  have hy : y s t+6*m s t+6=4^(m s t+1)*(3*m s t+4) := by
    simpa only [d,b] using y_eq s t
  have hpow : 2^(2*m s t+2)=4^(m s t+1) := by
    rw [show 2*m s t+2=2*(m s t+1) by omega,Nat.pow_mul,show 2^2=4 by decide]
  rw [hpow]
  have hr : 3*m s t+1+3=3*m s t+4 := by omega
  rw [hr]
  omega

#print axioms target_halt_eq
end FanArithmetic
