import GInverse
import P1TwoSector
import P1DualValuation

namespace BB6.P1SecondFan
open BB6.P1Reduction

private theorem inverse_three_general (b d k c : Nat)
    (h : GAncestor b d k c) :
    ∀ w : Nat, b=48*w+4 → d=16*w+7 →
      (k=12*w ∧ c=40*w+9) ∨
      (k=22*w+2 ∧ c=20*w+3) ∨
      (k=27*w+3 ∧ c=10*w) := by
  induction h with
  | upper k d =>
    intro w hb hd
    left
    constructor <;> omega
  | nest b d k c h ih =>
    intro w hb hd
    rcases ih w hb hd with ⟨hk,hc⟩ | ⟨hk,hc⟩ | ⟨hk,hc⟩
    · right
      left
      constructor <;> omega
    · right
      right
      constructor <;> omega
    · omega

/-- Exact source GAncestor classification for the odd-q second feeder. -/
theorem inverse_three (w k c : Nat)
    (h : GAncestor (48*w+4) (16*w+7) k c) :
    (k=12*w ∧ c=40*w+9) ∨
    (k=22*w+2 ∧ c=20*w+3) ∨
    (k=27*w+3 ∧ c=10*w) :=
  inverse_three_general _ _ _ _ h w rfl rfl

def w2 (q : Nat) : Nat := (BB6.Agent45TwoRoot.u2 q-1)/8

theorem odd_w2_identity (q : Nat) (hq : 1≤q) (hodd : q%2=1) :
    8*w2 q+1 = BB6.Agent45TwoRoot.u2 q := by
  have hx : 8 ∣ 2^(16*q) := by
    simpa using (Nat.pow_dvd_pow 2 (by omega : 3≤16*q))
  have hmod : 2^(16*q)%8=0 := Nat.dvd_iff_mod_eq_zero.mp hx
  have hlower := BB6.P1DualValuation.feeder_u_lower q hq
  have hu : BB6.Agent45TwoRoot.u2 q+4*q+3=7*2^(16*q) := by
    dsimp only [BB6.Agent45TwoRoot.u2]
    omega
  dsimp only [w2]
  omega

/-- All three source-level G-inverses of the L2 feeder when q is odd. -/
theorem odd_second_inverse_three_source (q k c : Nat)
    (hq : 1≤q) (hodd : q%2=1)
    (h : GAncestor (6*BB6.Agent45TwoRoot.u2 q-2)
        (2*BB6.Agent45TwoRoot.u2 q+5) k c) :
    (k=12*w2 q ∧ c=40*w2 q+9) ∨
    (k=22*w2 q+2 ∧ c=20*w2 q+3) ∨
    (k=27*w2 q+3 ∧ c=10*w2 q) := by
  have hrelation := odd_w2_identity q hq hodd
  have hb : 6*BB6.Agent45TwoRoot.u2 q-2=48*w2 q+4 := by omega
  have hd : 2*BB6.Agent45TwoRoot.u2 q+5=16*w2 q+7 := by omega
  rw [hb,hd] at h
  exact inverse_three (w2 q) k c h

/-- The remaining even-right ancestor fails the established P1 power shape. -/
theorem odd_last_power_gap (q j : Nat) (hq : 1≤q) (hodd : q%2=1) :
    54*w2 q+14 ≠ 14*2^j := by
  have hw := odd_w2_identity q hq hodd
  have hmass : 8*w2 q+4*q+4=7*2^(16*q) := by
    have hu : BB6.Agent45TwoRoot.u2 q+4*q+3=7*2^(16*q) := by
      have hb:=BB6.P1DualValuation.feeder_u_lower q hq
      dsimp only [BB6.Agent45TwoRoot.u2]
      omega
    omega
  have hp := BB6.P1DualValuation.feeder_power_large q hq
  have hbound : 28*2^(16*q)<54*w2 q+14 ∧
      54*w2 q+14 < 56*2^(16*q) := by omega
  have hp1 : 2^(16*q+1)=2*2^(16*q) := by
    rw [Nat.pow_succ]
    omega
  have hp2 : 2^(16*q+2)=4*2^(16*q) := by
    rw [show 16*q+2=(16*q)+2 by omega, Nat.pow_add,
      show (2:Nat)^2=4 by decide]
    omega
  intro heq
  by_cases hj : j≤16*q+1
  · have hle : 2^j ≤ 2^(16*q+1) :=
      Nat.pow_le_pow_right (by decide) hj
    omega
  · have hge : 16*q+2≤j := by omega
    have hle : 2^(16*q+2) ≤ 2^j :=
      Nat.pow_le_pow_right (by decide) hge
    omega

#print axioms odd_last_power_gap
#print axioms odd_w2_identity
#print axioms odd_second_inverse_three_source
#print axioms inverse_three
end BB6.P1SecondFan
