import GeneralM
import GeneralM3
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19OddTower
open BB6.Agent4Four
open BB6.Agent46

private theorem pow_growth (u : Nat) :
    u+3 ≤ (2:Nat)^u*44 := by
  induction u with
  | zero => decide
  | succ u ih =>
      have hp : (2:Nat)^(u+1)*44=2*((2:Nat)^u*44) := by
        rw [Nat.pow_succ]
        ac_rfl
      rw [hp]
      omega

private theorem gain_ge (r m t : Nat) (hr : 2≤r) (hm : m≤r) :
    m+1 ≤ (2:Nat)^(r-2)*(16*t+44) := by
  have hc := pow_growth (r-2)
  have hr_eq : r=(r-2)+2 := by omega
  have hmult : (2:Nat)^(r-2)*44 ≤ (2:Nat)^(r-2)*(16*t+44) := by
    exact Nat.mul_le_mul_left ((2:Nat)^(r-2)) (by omega)
  omega

private theorem band_plus_two (r t : Nat) :
    bandY r t+2=(2:Nat)^r*(16*t+44) := by
  have hp : 2≤(2:Nat)^r*(16*t+44) := by
    have powpos : 1≤(2:Nat)^r := Nat.pow_pos (by decide)
    have hmul := Nat.mul_le_mul_right (16*t+44) powpos
    omega
  dsimp [bandY]
  exact Nat.sub_add_cancel hp

private theorem band_scale (r e t : Nat) :
    bandY (r+e) t+2=(2:Nat)^e*(bandY r t+2) := by
  calc
    bandY (r+e) t+2 = (2:Nat)^(r+e)*(16*t+44) := band_plus_two _ _
    _ = (2:Nat)^e*((2:Nat)^r*(16*t+44)) := by
      rw [Nat.pow_add]
      ac_rfl
    _ = (2:Nat)^e*(bandY r t+2) := by rw [band_plus_two]

private theorem band_quarter (r t : Nat) (hr : 2≤r) :
    bandY r t+2=4*((2:Nat)^(r-2)*(16*t+44)) := by
  rw [band_plus_two]
  have he : r=(r-2)+2 := by omega
  have hp : (2:Nat)^r=4*(2:Nat)^(r-2) := by
    calc
      (2:Nat)^r=(2:Nat)^((r-2)+2) := by rw [←he]
      _ = (2:Nat)^(r-2)*(2:Nat)^2 := Nat.pow_add 2 (r-2) 2
      _ = 4*(2:Nat)^(r-2) := by
        simp only [show (2:Nat)^2=4 by decide]
        ac_rfl
  rw [hp]
  ac_rfl

def R (m r0 h : Nat) : Nat := r0+(2*m+2)*h

def S (m r0 s0 t : Nat) : Nat → Nat
  | 0 => s0
  | h+1 =>
      S m r0 s0 t h +
        2^(R m r0 h-2)*(16*t+44)-(m+1)

def J (m r0 s0 t h : Nat) : Nat := 4*S m r0 s0 t h+2*R m r0 h+2

def K (m r0 t h : Nat) : Nat := bandY (R m r0 h) t

private theorem R_succ (m r0 h : Nat) :
    R m r0 (h+1)=R m r0 h+(2*m+2) := by
  dsimp [R]
  rw [Nat.mul_succ]
  omega

private theorem R_lower (m r0 h : Nat)
    (hr0 : 2≤r0) (hm0 : m≤r0) :
    2≤R m r0 h ∧ m≤R m r0 h := by
  dsimp [R]
  omega

private theorem J_succ (m r0 s0 t h : Nat)
    (hr0 : 2≤r0) (hm0 : m≤r0) :
    J m r0 s0 t (h+1) =
      J m r0 s0 t h + K m r0 t h + 2 := by
  let rr := R m r0 h
  let ss := S m r0 s0 t h
  let gain := (2:Nat)^(rr-2)*(16*t+44)
  have hr := R_lower m r0 h hr0 hm0
  have hg : m+1≤gain := gain_ge rr m t hr.1 hr.2
  have hs : S m r0 s0 t (h+1)+(m+1)=ss+gain := by
    change (ss+gain-(m+1))+(m+1)=ss+gain
    exact Nat.sub_add_cancel (by omega)
  have hk : K m r0 t h+2=4*gain := by
    dsimp [K,gain,rr]
    exact band_quarter _ _ hr.1
  have hrr := R_succ m r0 h
  dsimp [J]
  omega

private theorem K_succ (m r0 t h : Nat) :
    K m r0 t (h+1)+2 =
      (2:Nat)^(2*m+2)*(K m r0 t h+2) := by
  unfold K
  rw [R_succ]
  exact band_scale _ _ _

/-- Every source stopping target in the level-r strict-image cylinder
    produces an infinite tower of further stopping targets for fixed m. -/
theorem tower_stopping (m r0 s0 t h : Nat)
    (hr0 : 2≤r0) (hm0 : m≤r0)
    (hbase : K m r0 t 0+J m r0 s0 t 0+3*m+5 =
      (2:Nat)^(2*m+2)*(J m r0 s0 t 0+3)) :
    K m r0 t h+J m r0 s0 t h+3*m+5 =
      (2:Nat)^(2*m+2)*(J m r0 s0 t h+3) := by
  induction h with
  | zero => exact hbase
  | succ h ih =>
      have hj := J_succ m r0 s0 t h hr0 hm0
      have hk := K_succ m r0 t h
      let p := (2:Nat)^(2*m+2)
      have hmul :
          p*(J m r0 s0 t (h+1)+3)=
          p*(J m r0 s0 t h+3)+p*(K m r0 t h+2) := by
        rw [hj]
        have he : J m r0 s0 t h+K m r0 t h+2+3 =
            (J m r0 s0 t h+3)+(K m r0 t h+2) := by omega
        rw [he,Nat.mul_add]
      rw [hmul]
      rw [←ih]
      have hks : p*(K m r0 t h+2)=K m r0 t (h+1)+2 := hk.symm
      rw [hks]
      rw [hj]
      omega

/-- The tower target is excluded for ALL blank-section times. -/
theorem tower_blank_excluded (m r0 s0 t h time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*J m r0 s0 t h+3,K m r0 t h) := by
  have hx : 2*J m r0 s0 t h+3 =
      8*S m r0 s0 t h+7+4*R m r0 h := by
    dsimp [J]
    omega
  rw [hx]
  exact blank_excludes_all_depth_cylinders
    (R m r0 h) (S m r0 s0 t h) t time

/-- The complete m=4a+1 high-stopping tower, at every additional
    depth (2m+2)*h, and all original blank-section times. -/
theorem m1_tower_stopping (a q h : Nat) :
    K (BB6.Agent19GeneralM.m a) (8*a+2) (BB6.Agent19GeneralM.t a q) h+
    J (BB6.Agent19GeneralM.m a) (8*a+2)
      (BB6.Agent19GeneralM.s a q) (BB6.Agent19GeneralM.t a q) h+
      3*BB6.Agent19GeneralM.m a+5 =
    (2:Nat)^(2*BB6.Agent19GeneralM.m a+2)*
      (J (BB6.Agent19GeneralM.m a) (8*a+2)
        (BB6.Agent19GeneralM.s a q) (BB6.Agent19GeneralM.t a q) h+3) := by
  apply tower_stopping
    (BB6.Agent19GeneralM.m a) (8*a+2)
    (BB6.Agent19GeneralM.s a q) (BB6.Agent19GeneralM.t a q) h
    (by omega) (by dsimp [BB6.Agent19GeneralM.m]; omega)
  have hj : BB6.Agent19GeneralM.j a q =
      4*BB6.Agent19GeneralM.s a q+2*(8*a+2)+2 := by
    dsimp [BB6.Agent19GeneralM.j]
    omega
  have hbase := BB6.Agent19GeneralM.general_high_stopping a q
  simpa only [K,J,R,S,Nat.mul_zero,Nat.add_zero,BB6.Agent19GeneralM.k,hj] using hbase

theorem m1_tower_unreachable (a q h time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*J (BB6.Agent19GeneralM.m a) (8*a+2)
        (BB6.Agent19GeneralM.s a q) (BB6.Agent19GeneralM.t a q) h+3,
        K (BB6.Agent19GeneralM.m a) (8*a+2)
          (BB6.Agent19GeneralM.t a q) h) := by
  exact tower_blank_excluded _ _ _ _ _ _

/-- The distinct m=4a+3 tower, across every extra source-image depth. -/
theorem m3_tower_stopping (a q h : Nat) :
    K (BB6.Agent19GeneralM3.m a) (8*a+5) (BB6.Agent19GeneralM3.t a q) h+
    J (BB6.Agent19GeneralM3.m a) (8*a+5)
      (BB6.Agent19GeneralM3.s a q) (BB6.Agent19GeneralM3.t a q) h+
      3*BB6.Agent19GeneralM3.m a+5 =
    (2:Nat)^(2*BB6.Agent19GeneralM3.m a+2)*
      (J (BB6.Agent19GeneralM3.m a) (8*a+5)
        (BB6.Agent19GeneralM3.s a q) (BB6.Agent19GeneralM3.t a q) h+3) := by
  apply tower_stopping
    (BB6.Agent19GeneralM3.m a) (8*a+5)
    (BB6.Agent19GeneralM3.s a q) (BB6.Agent19GeneralM3.t a q) h
    (by omega) (by dsimp [BB6.Agent19GeneralM3.m]; omega)
  have hj : BB6.Agent19GeneralM3.j a q =
      4*BB6.Agent19GeneralM3.s a q+2*(8*a+5)+2 := by
    dsimp [BB6.Agent19GeneralM3.j,BB6.Agent19GeneralM3.m]
    omega
  have hbase := BB6.Agent19GeneralM3.general_high_stopping a q
  simpa only [K,J,R,S,Nat.mul_zero,Nat.add_zero,BB6.Agent19GeneralM3.k,BB6.Agent19GeneralM3.r,hj] using hbase

theorem m3_tower_unreachable (a q h time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (2*J (BB6.Agent19GeneralM3.m a) (8*a+5)
        (BB6.Agent19GeneralM3.s a q) (BB6.Agent19GeneralM3.t a q) h+3,
        K (BB6.Agent19GeneralM3.m a) (8*a+5)
          (BB6.Agent19GeneralM3.t a q) h) := by
  exact tower_blank_excluded _ _ _ _ _ _

#print axioms m1_tower_stopping
#print axioms m1_tower_unreachable
#print axioms m3_tower_stopping
#print axioms m3_tower_unreachable
#print axioms tower_stopping
#print axioms tower_blank_excluded
end BB6.Agent19OddTower
