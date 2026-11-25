import OddEvenNonPowerParentFan
import AffineH5Quarter
import Lean.Elab.Tactic.Omega

#check Nat.div_pos
#check Nat.div_lt_iff_lt_mul
#check Nat.mod_add_div

namespace BB6.Agent34H5OddBridge

open BB6.Agent3OddEvenFan
open BB6.Agent46

def h5OddJ (r : Nat) : Nat := 2098495 + 4194304*r
def h5OddM (r w : Nat) : Nat := 4876330 + 4194304*r + 8388608*w
def h5OddExp (r w : Nat) : Nat := 9752639 + 8388608*r + 16777216*w
def h5OddD (r w : Nat) : Nat := 2 + 2*r + 3*w
def h5OddT (r w : Nat) : Nat := 2^(h5OddExp r w) * (h5OddJ r + 3)
def h5OddB (r w : Nat) : Nat := h5OddT r w - h5OddD r w
def h5OddK (r w : Nat) : Nat := 49726 + 2^23*h5OddB r w

def h5OddC (r w : Nat) : Nat :=
  2567283 + 2208205*r + 4416411*w
def h5OddA (r w : Nat) : Nat := 1472137 * h5OddT r w
def h5OddQ (r w : Nat) : Nat :=
  376991 + 736069*r + 1472137*h5OddB r w

def h5OddEax (r w : Nat) : Nat :=
  1735479 + 3388496*r + 6776976*h5OddB r w
def h5OddEay (r w : Nat) : Nat :=
  1280448 + 2500056*r + 5000120*h5OddB r w

theorem nat_succ_le_two_pow (n : Nat) : n+1 ≤ 2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      have hp : 0 < 2^n := Nat.pow_pos (by decide)
      have hpow : 2^(n+1) = 2^n + 2^n := by
        rw [Nat.pow_succ]
        omega
      omega

theorem pow_two_mono {a b : Nat} (h : a ≤ b) : 2^a ≤ 2^b := by
  induction b with
  | zero =>
      have ha : a=0 := by omega
      simp [ha]
  | succ b ih =>
      by_cases hab : a ≤ b
      · have hle := ih hab
        have hp : 0 < 2^b := Nat.pow_pos (by decide)
        have hstep : 2^b ≤ 2^(b+1) := by
          rw [Nat.pow_succ]
          omega
        omega
      · have ha : a=b+1 := by omega
        simp [ha]

theorem h5OddB_add_D (r w : Nat) :
    h5OddB r w + h5OddD r w = h5OddT r w := by
  have hlin : h5OddD r w < h5OddExp r w + 1 := by
    dsimp [h5OddD, h5OddExp]
    omega
  have hpow : h5OddExp r w + 1 ≤ 2^(h5OddExp r w) :=
    nat_succ_le_two_pow (h5OddExp r w)
  have hj : 1 ≤ h5OddJ r + 3 := by
    dsimp [h5OddJ]
    omega
  have hmul : 2^(h5OddExp r w) ≤
      2^(h5OddExp r w) * (h5OddJ r + 3) := by
    have h := Nat.mul_le_mul_left (2^(h5OddExp r w)) hj
    simpa using h
  have hdle : h5OddD r w ≤ h5OddT r w := by
    dsimp [h5OddT]
    omega
  dsimp [h5OddB]
  exact Nat.sub_add_cancel hdle

theorem h5OddK_gate (r w : Nat) :
    h5OddK r w + h5OddJ r + 3*h5OddM r w + 5 =
      2^(2*h5OddM r w+2)*(h5OddJ r+3) := by
  have hexp : h5OddExp r w + 23 = 2*h5OddM r w + 2 := by
    dsimp [h5OddExp, h5OddM]
    omega
  have hlinear :
      h5OddJ r + 3*h5OddM r w + 5 + 49726 =
        2^23*h5OddD r w := by
    dsimp [h5OddJ, h5OddM, h5OddD]
    omega
  have hpow :
      2^(2*h5OddM r w+2)*(h5OddJ r+3) =
        2^23*h5OddT r w := by
    rw [← hexp, Nat.pow_add]
    dsimp [h5OddT]
    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  calc
    h5OddK r w + h5OddJ r + 3*h5OddM r w + 5
        = 2^23*h5OddB r w +
          (h5OddJ r + 3*h5OddM r w + 5 + 49726) := by
            dsimp [h5OddK]
            omega
    _ = 2^23*h5OddB r w + 2^23*h5OddD r w := by
          rw [hlinear]
    _ = 2^23*(h5OddB r w + h5OddD r w) := by
          rw [Nat.mul_add]
    _ = 2^23*h5OddT r w := by
          rw [h5OddB_add_D]
    _ = 2^(2*h5OddM r w+2)*(h5OddJ r+3) := by
          rw [hpow]

theorem h5OddQ_add_C_eq_A (r w : Nat) :
    h5OddQ r w + h5OddC r w = h5OddA r w := by
  have hbd := h5OddB_add_D r w
  calc
    h5OddQ r w + h5OddC r w =
        1472137*(h5OddB r w + h5OddD r w) := by
          dsimp [h5OddQ, h5OddC, h5OddD]
          omega
    _ = h5OddA r w := by
          dsimp [h5OddA]
          rw [hbd]

theorem h5OddT_eq_pow (r w : Nat) :
    h5OddT r w =
      2^(h5OddExp r w+1)*(1049249+2097152*r) := by
  have hj3 : h5OddJ r + 3 =
      2*(1049249 + 2097152*r) := by
    dsimp [h5OddJ]
    omega
  dsimp [h5OddT]
  rw [hj3, Nat.pow_succ]
  simp [Nat.mul_assoc]

theorem h5OddA_divisible (r w : Nat) :
    2^(h5OddExp r w+1) ∣ h5OddA r w := by
  have hT := h5OddT_eq_pow r w
  refine ⟨1472137*(1049249+2097152*r), ?_⟩
  dsimp [h5OddA]
  rw [hT]
  simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

theorem h5OddC_lt_pow (r w : Nat) :
    h5OddC r w < 2^(h5OddExp r w) := by
  have hlin : h5OddC r w < h5OddExp r w + 1 := by
    dsimp [h5OddC, h5OddExp]
    omega
  have hpow := nat_succ_le_two_pow (h5OddExp r w)
  omega

theorem h5OddQ_not_pow (r w k : Nat) :
    h5OddQ r w ≠ 2^k := by
  intro hQ
  let e := h5OddExp r w
  let p := 2^(e+1)
  have hQC := h5OddQ_add_C_eq_A r w
  have hAdiv : p ∣ h5OddA r w := by
    simpa [p, e] using h5OddA_divisible r w
  have hCpos : 0 < h5OddC r w := by
    dsimp [h5OddC]
    omega
  have hCsmall : h5OddC r w < 2^e := by
    simpa [e] using h5OddC_lt_pow r w
  have hp : 0 < p := by
    dsimp [p]
    exact Nat.pow_pos (by decide)
  have hpEq : p = 2^e + 2^e := by
    dsimp [p]
    rw [Nat.pow_succ]
    omega
  have hC_lt_p : h5OddC r w < p := by omega
  have hmod0 : (h5OddQ r w + h5OddC r w) % p = 0 := by
    rw [hQC]
    exact Nat.mod_eq_zero_of_dvd hAdiv
  rw [Nat.add_mod, Nat.mod_eq_of_lt hC_lt_p] at hmod0
  have hsumdiv : p ∣ h5OddQ r w % p + h5OddC r w :=
    Nat.dvd_of_mod_eq_zero hmod0
  have hqmodlt : h5OddQ r w % p < p := Nat.mod_lt _ hp
  have hsumPos : 0 < h5OddQ r w % p + h5OddC r w := by omega
  have hsumLt : h5OddQ r w % p + h5OddC r w < 2*p := by omega
  have hple : p ≤ h5OddQ r w % p + h5OddC r w :=
    Nat.le_of_dvd hsumPos hsumdiv
  have hquotpos : 0 <
      (h5OddQ r w % p + h5OddC r w) / p :=
    Nat.div_pos hple hp
  have hquotlt :
      (h5OddQ r w % p + h5OddC r w) / p < 2 :=
    (Nat.div_lt_iff_lt_mul hp).2 hsumLt
  have hquotEq :
      (h5OddQ r w % p + h5OddC r w) / p = 1 := by omega
  have hsumEq :
      h5OddQ r w % p + h5OddC r w = p := by
    have hdecomp := Nat.mod_add_div
      (h5OddQ r w % p + h5OddC r w) p
    rw [hmod0, hquotEq] at hdecomp
    omega
  have hQmod : h5OddQ r w % p = p - h5OddC r w := by omega
  have hbig : 2^e < p - h5OddC r w := by omega
  by_cases hk : k ≤ e
  · have hpowle : 2^k ≤ 2^e := pow_two_mono hk
    have hpowlt : 2^k < p := by omega
    have hpowmod : (2^k) % p = 2^k := Nat.mod_eq_of_lt hpowlt
    rw [hQ, hpowmod] at hQmod
    omega
  · have hk' : e+1 ≤ k := by omega
    have hdiv : p ∣ 2^k := by
      dsimp [p]
      exact Nat.pow_dvd_pow 2 hk'
    have hpowmod : (2^k) % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
    rw [hQ, hpowmod] at hQmod
    omega

theorem h5OddMass_eq (r w : Nat) :
    h5OddEax r w + h5OddEay r w + 1 = 8*h5OddQ r w := by
  dsimp [h5OddEax, h5OddEay, h5OddQ]
  omega

theorem h5OddMass_not_power (r w : Nat) :
    ∀ n : Nat, h5OddEax r w + h5OddEay r w + 1 ≠ 2^n := by
  intro n hpow
  have hmass := h5OddMass_eq r w
  have hqpos : 1 ≤ h5OddQ r w := by
    dsimp [h5OddQ]
    omega
  by_cases hn : n ≤ 2
  · have hpowle : 2^n ≤ 2^2 := pow_two_mono hn
    have hpowle4 : 2^n ≤ 4 := by simpa using hpowle
    have hlow : 8 ≤ 8*h5OddQ r w :=
      Nat.mul_le_mul_left 8 hqpos
    rw [hmass] at hpow
    omega
  · have hn3 : 3 ≤ n := by omega
    let k := n-3
    have hk : n = k+3 := by dsimp [k]; omega
    have hpow' : 2^n = 8*2^k := by
      calc
        2^n = 2^(k+3) := by rw [hk]
        _ = 2^k*2^3 := by rw [Nat.pow_add]
        _ = 8*2^k := by simp [Nat.mul_comm]
    rw [hmass, hpow'] at hpow
    have hq : h5OddQ r w = 2^k := by omega
    exact h5OddQ_not_pow r w k hq

theorem h5Odd_parent_fan (r w : Nat) :
    (∃ t, BB6.Agent8Section.run secNext t (some (5,1)) =
        some (h5OddEax r w, h5OddEay r w)) ↔
      (∃ t, BB6.Agent8Section.run secNext t (some (5,1)) =
        some (h5OddEax r w + h5OddEay r w - 2,
             (h5OddEay r w - 2)/2)) ∨
      (∃ n a k t, n%2=1 ∧ a%2=1 ∧ 3≤a ∧ a<2*k ∧
        h5OddEax r w + h5OddEay r w + 1 = 2^(n+1)*(a+3) ∧
        2*k+a+7+3*n = h5OddEax r w + 2*h5OddEay r w ∧
        BB6.Agent8Section.run secNext t (some (5,1)) = some (a,k)) := by
  exact BB6.Agent3OddEvenFan.blank_reach_iff_odd_even_nonpower_parent_fan
    (h5OddEax r w) (h5OddEay r w)
    (by dsimp [h5OddEax]; omega)
    (by dsimp [h5OddEax]; omega)
    (by dsimp [h5OddEay]; omega)
    (by dsimp [h5OddEay]; omega)
    (h5OddMass_not_power r w)

theorem h5OddQuarterSource (r w : Nat)
    (hg : BB6.Agent25OddLift.h5PhaseGuard r w) :
    ¬ BB6.Agent25OddLift.Reach secNext
        (2*h5OddJ r+3) (h5OddK r w) := by
  have hgate := h5OddK_gate r w
  have hsrc :=
    BB6.Agent25OddLift.h5QuarterHighSource r w (h5OddK r w) hg hgate
  simpa [h5OddJ, h5OddM,
    BB6.Agent25OddLift.h5J, BB6.Agent25OddLift.h5M] using hsrc

#print BB6.Agent25OddLift.h5J
#print BB6.Agent25OddLift.h5M
#check BB6.Agent25OddLift.h5QuarterHighSource


#print axioms BB6.Agent34H5OddBridge.h5OddQ_not_pow
#print axioms BB6.Agent34H5OddBridge.h5OddMass_not_power
#print axioms BB6.Agent34H5OddBridge.h5Odd_parent_fan
#print axioms BB6.Agent34H5OddBridge.h5OddQuarterSource

end BB6.Agent34H5OddBridge
