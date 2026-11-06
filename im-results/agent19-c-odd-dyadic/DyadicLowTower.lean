import DyadicSixCone
import OddOddLowVal
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace BB6.Agent19SixCone
open BB6.Agent46 BB6.Agent3

/-- Arbitrarily deep source-exact forbidden low-target tower. The exponent
n is unbounded. The even parity and odd-part congruence force the unique
odd/odd predecessor to enter the global dyadic even-right missing cone. -/
theorem odd_gate_dyadic_tower_no_blank (n k u : Nat)
    (hn : 2≤n) (hne : n%2=0)
    (hu : 9≤u) (hu4 : u%4=1)
    (hgate : 3*k=2^(n+2)*u+1) :
    ¬ BB6.Agent3.CReach 1 k := by
  have hpow : 16 ∣ (2:Nat)^(n+2) := by
    change (2:Nat)^4 ∣ 2^(n+2)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨v,hv⟩ := hpow
  have h3k : 3*k=16*(v*u)+1 := by
    calc
      3*k=2^(n+2)*u+1 := hgate
      _ = 16*(v*u)+1 := by rw [hv]; simp only [Nat.mul_assoc]
  have hk16 : k%16=11 := by omega
  have hkbig : 24≤k+1 := by
    have hvpos : 1≤v := by
      have hppos : 0<(2:Nat)^(n+2) := Nat.pow_pos (by decide)
      omega
    have hmul : u≤v*u := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right u hvpos
    have hlarge : 9≤v*u := by omega
    omega
  let a := (1+k-4)/2
  let b := (1+3*k-10)/4
  have hrel1 : 1+k=2*a+4 := by dsimp [a]; omega
  have hrel2 : 1+3*k=4*b+10 := by dsimp [b]; omega
  have hfactor : (2:Nat)^(n+2)=4*2^n := by
    rw [Nat.pow_add]
    have hfour : (2:Nat)^2=4 := by decide
    rw [hfour]
    omega
  have h3k2 : 3*k=4*(2^n*u)+1 := by
    calc
      3*k=2^(n+2)*u+1 := hgate
      _ = 4*(2^n*u)+1 := by rw [hfactor]; simp only [Nat.mul_assoc]
  have hb : b+2=2^n*u := by omega
  have hmass : a+2*b+6=2*k := by omega
  have hcong : (a+2*b+4*n)%8=0 := by omega
  intro hr
  have hpred := (BB6.Agent3.oddodd_lowval_blank_reach_iff 1 k
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).mp hr
  change BB6.Agent3.CReach _ _ at hpred
  have hpred0 : BB6.Agent3.CReach a b := by
    simpa only [a,b] using hpred
  exact (dyadic_six_cone_no_blank n a b u hu hu4 hb hcong) hpred0

#print axioms odd_gate_dyadic_tower_no_blank
end BB6.Agent19SixCone
