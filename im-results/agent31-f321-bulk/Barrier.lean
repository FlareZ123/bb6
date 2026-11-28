import Lean
import Lean.Elab.Tactic.Omega
namespace BB6.Agent31F321Density

/-- A high reverse step preserves the exponential lower bound. -/
theorem big_next_high (n D D':Nat)
 (hb:6*2^(n+1)≤D+3)
 (h:D=2*D'+3) :
 6*2^n≤D'+3 := by
 rw [Nat.pow_succ] at hb
 omega

/-- A far reverse step can only increase the second counter. -/
theorem big_next_far (n D D':Nat)
 (hb:6*2^(n+1)≤D+3)
 (h:D≤D') :
 6*2^n≤D'+3 := by
 rw [Nat.pow_succ] at hb
 omega

theorem big_implies_large (n D:Nat) (hb:6*2^n≤D+3):3≤D := by
 have hp : 0<2^n := Nat.pow_pos (by decide : 0 < 2)
 omega

#print axioms big_next_high
#print axioms big_next_far
#print axioms big_implies_large
end BB6.Agent31F321Density
