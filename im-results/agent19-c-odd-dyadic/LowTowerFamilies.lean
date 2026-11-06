import DyadicLowTower
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19SixCone
open BB6.Agent46 BB6.Agent3

/-- The arithmetic inverse index for a dyadic exponent shifted by six. -/
def indexShift (m : Nat) : Nat → Nat
  | 0 => m
  | t+1 => 64*indexShift m t+91

private theorem indexShift_base (m t : Nat) :
    m≤indexShift m t := by
  induction t with
  | zero => simp [indexShift]
  | succ t ih =>
      simp only [indexShift]
      omega

private theorem indexShift_lower (m n t : Nat) (hbase : n+4≤m) :
    n+6*t+4 ≤ indexShift m t := by
  induction t with
  | zero => simpa [indexShift] using hbase
  | succ t ih =>
      simp only [indexShift]
      omega

private theorem indexShift_linear (m n r t : Nat)
    (hbase : 9*m+13+5*(2:Nat)^(n+2)=r*2^(n+4)) :
    9*indexShift m t+13+5*(2:Nat)^(n+6*t+2) =
    r*2^(n+6*t+4) := by
  induction t with
  | zero => simpa [indexShift] using hbase
  | succ t ih =>
      have hpowA : (2:Nat)^(n+6*(t+1)+2) =
          64*2^(n+6*t+2) := by
        have he : n+6*(t+1)+2=(n+6*t+2)+6 := by omega
        rw [he,Nat.pow_add,show (2:Nat)^6=64 by decide]
        omega
      have hpowB : (2:Nat)^(n+6*(t+1)+4) =
          64*2^(n+6*t+4) := by
        have he : n+6*(t+1)+4=(n+6*t+4)+6 := by omega
        rw [he,Nat.pow_add,show (2:Nat)^6=64 by decide]
        omega
      change 9*(64*indexShift m t+91)+13+5*2^(n+6*(t+1)+2)=
        r*2^(n+6*(t+1)+4)
      rw [hpowA,hpowB]
      calc
        9*(64*indexShift m t+91)+13+5*(64*2^(n+6*t+2)) =
          64*(9*indexShift m t+13+5*2^(n+6*t+2)) := by omega
        _ = 64*(r*2^(n+6*t+4)) := by rw [ih]
        _ = r*(64*2^(n+6*t+4)) := by ac_rfl

/-- An exact low-family stopping equation plus a dyadic index relation
is impossible on Machine C's authentic blank section orbit. -/
private theorem four_linear_power (m : Nat) :
    4*m+4 ≤ (2:Nat)^(m+5) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : m+1+5=(m+5)+1 := by omega
      rw [he,Nat.pow_succ]
      omega

theorem low_linear_stop_no_root (n m k r : Nat)
    (hn : 2≤n) (hne : n%2=0) (hm : n+4≤m) (hr : r≤m)
    (hlin : 9*m+13+5*(2:Nat)^(n+2)=r*2^(n+4))
    (hstop : k+3*m+4=2^(2*m+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  let Q := (2:Nat)^(n+2)
  let T := (2:Nat)^(2*m-n+1)
  have he : (n+2)+(2*m-n+1)=2*m+3 := by omega
  have hpow : 2^(2*m+3)=Q*T := by
    dsimp [Q,T]
    rw [← he, Nat.pow_add]
  have hmodpow : 2^(n+4)=4*Q := by
    dsimp [Q]
    have he2 : n+4=(n+2)+2 := by omega
    rw [he2,Nat.pow_add,show (2:Nat)^2=4 by decide]
    omega
  have hlinTmp := hlin
  rw [hmodpow] at hlinTmp
  have hlin' : 9*m+13+5*Q=4*(r*Q) := by
    calc
      9*m+13+5*Q=r*(4*Q) := hlinTmp
      _=4*(r*Q) := by ac_rfl
  have hTpos : 0<T := Nat.pow_pos (by decide)
  have hd32 : 32∣T := by
    dsimp [T]
    change (2:Nat)^5 ∣ 2^(2*m-n+1)
    exact Nat.pow_dvd_pow 2 (by omega)
  have ht32 : 32≤T := Nat.le_of_dvd hTpos hd32
  have hpDiv : (2:Nat)^(m+5) ∣ T := by
    dsimp [T]
    exact Nat.pow_dvd_pow 2 (by omega)
  have htpow : (2:Nat)^(m+5) ≤ T :=
    Nat.le_of_dvd hTpos hpDiv
  have hTlinear : 4*m+4≤T := by
    have h := four_linear_power m
    omega
  let u := 3*T+5-4*r
  have hdiff : 4*r≤3*T+5 := by omega
  have hu : 9≤u := by dsimp [u]; omega
  have hueq : u+4*r=3*T+5 := by dsimp [u]; omega
  have hd4 : 4∣T := by
    dsimp [T]
    change (2:Nat)^2 ∣ 2^(2*m-n+1)
    exact Nat.pow_dvd_pow 2 (by omega)
  have htmod : T%4=0 := Nat.mod_eq_zero_of_dvd hd4
  have hu4 : u%4=1 := by omega
  have hmul : Q*u + 4*(r*Q) = 3*(Q*T)+5*Q := by
    calc
      Q*u+4*(r*Q)=Q*(u+4*r) := by
        rw [Nat.mul_add]
        congr 1
        ac_rfl
      _ = Q*(3*T+5) := by rw [hueq]
      _ = 3*(Q*T)+5*Q := by
        rw [Nat.mul_add]
        congr 1 <;> ac_rfl
  have hstop' : k+3*m+4=Q*T := by simpa only [hpow] using hstop
  have hthree : 3*k+9*m+12=3*(Q*T) := by omega
  have hku : 3*k=Q*u+1 := by omega
  exact odd_gate_dyadic_tower_no_blank n k u hn hne hu hu4
    (by simpa only [Q] using hku)

/-- One explicitly constructive surviving low-stopping depth at every
sixth even dyadic level; these levels are unbounded in t. -/
theorem low_shifted_depth_unreachable (t k : Nat)
    (hstop : k+3*(indexShift 539 t)+4=
      2^(2*(indexShift 539 t)+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hlin : 9*indexShift 539 t+13+5*(2:Nat)^(6+6*t+2) =
      6*2^(6+6*t+4) :=
    indexShift_linear 539 6 6 t (by decide)
  have hm : 6+6*t+4 ≤ indexShift 539 t :=
    indexShift_lower 539 6 t (by decide)
  have hne : (6+6*t)%2=0 := by omega
  have hr : 6 ≤ indexShift 539 t := by
    have h := indexShift_base 539 t
    omega
  exact low_linear_stop_no_root (6+6*t) (indexShift 539 t) k 6
    (by omega) hne hm hr hlin hstop


/-- Covers every second even dyadic depth from n=2. The base t=0
reproduces the earlier m=11 congruence representative. -/
theorem low_shifted_depth_two (t k : Nat)
    (hstop : k+3*(indexShift 11 t)+4=
      2^(2*(indexShift 11 t)+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hlin : 9*indexShift 11 t+13+5*(2:Nat)^(2+6*t+2) =
      3*2^(2+6*t+4) :=
    indexShift_linear 11 2 3 t (by decide)
  have hm : 2+6*t+4 ≤ indexShift 11 t :=
    indexShift_lower 11 2 t (by decide)
  have hne : (2+6*t)%2=0 := by omega
  have hr : 3 ≤ indexShift 11 t := by
    have h := indexShift_base 11 t
    omega
  exact low_linear_stop_no_root (2+6*t) (indexShift 11 t) k 3
    (by omega) hne hm hr hlin hstop

/-- Covers every second even dyadic depth from n=4. The base t=0
reproduces the earlier m=219 congruence representative. -/
theorem low_shifted_depth_four (t k : Nat)
    (hstop : k+3*(indexShift 219 t)+4=
      2^(2*(indexShift 219 t)+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hlin : 9*indexShift 219 t+13+5*(2:Nat)^(4+6*t+2) =
      9*2^(4+6*t+4) :=
    indexShift_linear 219 4 9 t (by decide)
  have hm : 4+6*t+4 ≤ indexShift 219 t :=
    indexShift_lower 219 4 t (by decide)
  have hne : (4+6*t)%2=0 := by omega
  have hr : 9 ≤ indexShift 219 t := by
    have h := indexShift_base 219 t
    omega
  exact low_linear_stop_no_root (4+6*t) (indexShift 219 t) k 9
    (by omega) hne hm hr hlin hstop

#print axioms low_shifted_depth_two
#print axioms low_shifted_depth_four


/-- Every arithmetic progression generated by a depth seed is inaccessible,
for all offsets s, with the modulus growing with the inverse depth. -/
theorem low_full_residue_progression (n M R s k : Nat)
    (hn : 2≤n) (hne : n%2=0) (hM : n+4≤M) (hR : R≤M)
    (hlin : 9*M+13+5*(2:Nat)^(n+2)=R*2^(n+4))
    (hstop : k+3*(M+2^(n+4)*s)+4=
      2^(2*(M+2^(n+4)*s)+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  let Q := (2:Nat)^(n+2)
  let L := (2:Nat)^(n+4)
  have hLpositive : 0<L := Nat.pow_pos (by decide)
  have hL16 : 16∣L := by
    dsimp [L]
    change (2:Nat)^4 ∣ 2^(n+4)
    exact Nat.pow_dvd_pow 2 (by omega)
  have hLbound : 9≤L := by
    have hh : 16≤L := Nat.le_of_dvd hLpositive hL16
    omega
  have hscale : 9*s≤L*s := Nat.mul_le_mul_right s hLbound
  have hmExt : n+4≤M+L*s := by omega
  have hrExt : R+9*s≤M+L*s := by omega
  have hlinExt : 9*(M+L*s)+13+5*Q=(R+9*s)*L := by
    calc
      9*(M+L*s)+13+5*Q = (9*M+13+5*Q)+9*(L*s) := by omega
      _ = R*L + 9*(L*s) := by rw [hlin]
      _ = (R+9*s)*L := by rw [Nat.add_mul]; ac_rfl
  exact low_linear_stop_no_root n (M+L*s) k (R+9*s)
    hn hne hmExt hrExt (by simpa only [Q,L] using hlinExt)
    (by simpa only [L] using hstop)

/-- Every low parameter in this depth-dependent congruence class is
excluded from the actual Machine C blank section, without a finite cutoff. -/
theorem low_all_depth_two (t s k : Nat)
    (hstop : k+3*(indexShift 11 t+2^(2+6*t+4)*s)+4 =
      2^(2*(indexShift 11 t+2^(2+6*t+4)*s)+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hlin : 9*indexShift 11 t+13+5*(2:Nat)^(2+6*t+2) =
      3*2^(2+6*t+4) := indexShift_linear 11 2 3 t (by decide)
  have hm := indexShift_lower 11 2 t (by decide)
  have hR : 3≤indexShift 11 t := by
    have hh := indexShift_base 11 t
    omega
  exact low_full_residue_progression (2+6*t) (indexShift 11 t) 3 s k
    (by omega) (by omega) hm hR hlin hstop

theorem low_all_depth_four (t s k : Nat)
    (hstop : k+3*(indexShift 219 t+2^(4+6*t+4)*s)+4 =
      2^(2*(indexShift 219 t+2^(4+6*t+4)*s)+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hlin : 9*indexShift 219 t+13+5*(2:Nat)^(4+6*t+2) =
      9*2^(4+6*t+4) := indexShift_linear 219 4 9 t (by decide)
  have hm := indexShift_lower 219 4 t (by decide)
  have hR : 9≤indexShift 219 t := by
    have hh := indexShift_base 219 t
    omega
  exact low_full_residue_progression (4+6*t) (indexShift 219 t) 9 s k
    (by omega) (by omega) hm hR hlin hstop

theorem low_all_depth_six (t s k : Nat)
    (hstop : k+3*(indexShift 539 t+2^(6+6*t+4)*s)+4 =
      2^(2*(indexShift 539 t+2^(6+6*t+4)*s)+3)) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hlin : 9*indexShift 539 t+13+5*(2:Nat)^(6+6*t+2) =
      6*2^(6+6*t+4) := indexShift_linear 539 6 6 t (by decide)
  have hm := indexShift_lower 539 6 t (by decide)
  have hR : 6≤indexShift 539 t := by
    have hh := indexShift_base 539 t
    omega
  exact low_full_residue_progression (6+6*t) (indexShift 539 t) 6 s k
    (by omega) (by omega) hm hR hlin hstop

#print axioms low_full_residue_progression
#print axioms low_all_depth_two
#print axioms low_all_depth_four
#print axioms low_all_depth_six

#print axioms low_linear_stop_no_root
#print axioms low_shifted_depth_unreachable
end BB6.Agent19SixCone
