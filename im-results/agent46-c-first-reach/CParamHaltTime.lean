import BounceHalting
import FastSectionDef
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46ParamTime
open BB6.Agent46 BB6.Agent15

/-- Exact CLine call count for every terminal even-middle bounce seed. -/
theorem bounce_seed_time (k n : Nat) (hk : k%2=0) :
    (bounce k (haltSeed k n)).1 + 2*k + 5*n + 6 = 2^(n+1)*(k+4) := by
  induction n generalizing k with
  | zero =>
      have he : k%2≠1 := by omega
      simp [haltSeed,bounce,he]
      omega
  | succ n ih =>
      have hlarge := seed_succ_large k n
      have hlow : ¬ haltSeed k (n+1) < 4 := by omega
      have he : k%2≠1 := by omega
      have hc4 : haltSeed k (n+1) ≠ 4 := by omega
      have hc5 : haltSeed k (n+1) ≠ 5 := by omega
      have hs : ¬ haltSeed k (n+1) ≤ 2*k+8 := by omega
      have hc : haltSeed k (n+1)-(2*k+5)=haltSeed (2*k+4) n := by
        rw [haltSeed]; omega
      have hh := ih (2*k+4) (by omega)
      have hpow : 2^(n+1)*(2*k+8)=2^((n+1)+1)*(k+4) := by
        have h2 : 2*k+8=2*(k+4) := by omega
        rw [h2]
        calc
          2^(n+1)*(2*(k+4)) = (2^(n+1)*2)*(k+4) := by ac_rfl
          _ = 2^((n+1)+1)*(k+4) := by
            exact congrArg (fun z : Nat => z*(k+4)) (Nat.pow_succ 2 (n+1)).symm
      rw [bounce.eq_1]
      simp only [if_neg hlow,if_neg he,if_neg hc4,if_neg hc5,if_neg hs]
      rw [hc]
      have hK : 2*k+4+4=2*k+8 := by omega
      rw [hK, hpow] at hh
      omega

private theorem pow_eight_lower (m : Nat) : 3*m+8 ≤ 2^(2*m+3) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+3 = (2*m+3)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem pow_four_lower (m : Nat) : 3*m+4 ≤ 2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2 = (2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

private theorem pow_low_scale (m : Nat) :
    2^(2*m+1)*8 = 2^(2*m+4) := by
  have he : 2*m+4=(2*m+1)+3 := by omega
  calc
    2^(2*m+1)*8 = 2^(2*m+1)*2^3 := rfl
    _ = 2^((2*m+1)+3) := (Nat.pow_add 2 (2*m+1) 3).symm
    _ = 2^(2*m+4) := by rw [he]

private theorem pow_double_scale (m : Nat) :
    2*2^(2*m+3) = 2^(2*m+4) := by
  have he : 2*m+4=(2*m+3)+1 := by omega
  calc
    2*2^(2*m+3) = 2^(2*m+3)*2 := by omega
    _ = 2^((2*m+3)+1) := (Nat.pow_succ 2 (2*m+3)).symm
    _ = 2^(2*m+4) := by rw [he]

/-- Exact elapsed CLine time for every low-dyadic terminal section input. -/
theorem low_halting_time (k m : Nat)
    (hk : k+3*m+4 = 2^(2*m+3)) :
    secTime (1,k)+10*m+11 = 2^(2*m+4) := by
  have hbound := pow_eight_lower m
  have hkp : 4≤k := by omega
  have hs := seed_power_equation 4 (2*m)
  have hscale := pow_low_scale m
  have hdouble := pow_double_scale m
  have hc : 2*k-3 = haltSeed 4 (2*m) := by
    omega
  have ht : secTime (1,k) = 3 + (bounce 4 (2*k-3)).1 := by
    have hk0 : k≠0 := by omega
    have hk1 : k≠1 := by omega
    have hk2 : k≠2 := by omega
    have hk3 : k≠3 := by omega
    simp [secTime,exactSection,hk0,hk1,hk2,hk3]
  rw [hc] at ht
  have hb := bounce_seed_time 4 (2*m) (by decide)
  rw [ht]
  omega

/-- Exact elapsed CLine time for every high-dyadic terminal section input. -/
theorem high_halting_time (j k m : Nat)
    (hk : k+j+3*m+5 = 2^(2*m+2)*(j+3)) :
    secTime (2*j+3,k)+4*m+3 = 2*k := by
  have hpow := pow_four_lower m
  have h4 : 4≤2^(2*m+2) := by omega
  have hLeft : 4*j ≤ 2^(2*m+2)*j := Nat.mul_le_mul_right j h4
  have hRight : 3*(3*m+4) ≤ 3*2^(2*m+2) := Nat.mul_le_mul_left 3 hpow
  have hprod : 2^(2*m+2)*(j+3) = 2^(2*m+2)*j+3*2^(2*m+2) := by
    simp [Nat.mul_add,Nat.mul_comm]
  have hkp : 0<k := by omega
  have hdom : 2*j+3<2*k := by omega
  have htime : secTime (2*j+3,k) =
      (2*j+2) + (bounce (2*j+2) (2*k-(2*j+3)+3)).1 := by
    have ha0 : 2*j+3≠0 := by omega
    have ha1 : 2*j+3≠1 := by omega
    have hk0 : k≠0 := by omega
    have hd : ¬ 2*k≤2*j+3 := by omega
    simp [secTime,exactSection,ha0,ha1,hk0,hd]
  have hs := seed_power_equation (2*j+2) (2*m+1)
  have hscale : 2^(2*m+2)*(2*j+6) = 2*(2^(2*m+2)*(j+3)) := by
    have he : 2*j+6=2*(j+3) := by omega
    rw [he]
    ac_rfl
  have hc : 2*k-(2*j+3)+3 = haltSeed (2*j+2) (2*m+1) := by
    have hn : (2*m+1)+1=2*m+2 := by omega
    have heq : 2*j+2+4=2*j+6 := by omega
    rw [hn,heq,hscale] at hs
    omega
  rw [hc] at htime
  have hb := bounce_seed_time (2*j+2) (2*m+1) (by omega)
  rw [htime]
  have hn : (2*m+1)+1=2*m+2 := by omega
  have heq : 2*j+2+4=2*j+6 := by omega
  rw [hn,heq,hscale] at hb
  omega

#print axioms bounce_seed_time
#print axioms low_halting_time
#print axioms high_halting_time
end BB6.Agent46ParamTime
