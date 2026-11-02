import Std

namespace BB6.Agent1Quarter
private theorem pow16_dom_succ (q : Nat) : 64*(q+2) ≤ 2^(16*(q+1)) := by
  induction q with
  | zero => decide
  | succ q ih =>
    have hp : 2^(16*(q+1+1))=65536*2^(16*(q+1)) := by
      have he : 16*(q+1+1)=16*(q+1)+16 := by omega
      rw [he, Nat.pow_add]
      simp only [Nat.reducePow]
      omega
    rw [hp]
    omega

theorem pow16_dom (q : Nat) (hq : 1≤q) : 64*(q+1) ≤ 2^(16*q) := by
  cases q with
  | zero => omega
  | succ q =>
    simpa [Nat.succ_eq_add_one, Nat.add_assoc] using pow16_dom_succ q

private theorem no_pow_in_band (m z : Nat)
    (hl : 28*2^m < z) (hu : z < 56*2^m) :
    ∀ j : Nat, z ≠ 14*2^j := by
  intro j he
  by_cases hs : j ≤ m+1
  · have hp := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hs
    have hpow : 2^(m+1)=2*2^m := by rw [Nat.pow_succ]; omega
    omega
  · have hg : m+2 ≤ j := by omega
    have hp := Nat.pow_le_pow_right (show 0<(2:Nat) by decide) hg
    have hpow : 2^(m+2)=4*2^m := by
      rw [Nat.pow_add]
      simp only [Nat.reducePow]
      omega
    omega

/-- Any even-right potential predecessor in the numerical band is
    incompatible with the global reachable even-left 14-power shape. -/
theorem window_not_power (q u x : Nat) (hq : 1≤q)
    (hu : u+4*q+3=7*2^(16*q))
    (hl : 35*u≤8*x+100) (hh : 8*x≤61*u+100) :
    ∀ j : Nat, x+12 ≠ 14*2^j := by
  have he:=pow16_dom q hq
  have hlower : 28*2^(16*q)<x+12 := by omega
  have hupper : x+12<56*2^(16*q) := by omega
  exact no_pow_in_band (16*q) (x+12) hlower hupper

#print axioms window_not_power
end BB6.Agent1Quarter
