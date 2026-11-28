import BB429LastResetImproved

namespace BB429LastResetParamClosed
open BB429NewResidue

set_option maxHeartbeats 30000000
set_option maxRecDepth 30000

/-- The exact 128-fold exponent shift, for every relevant large last-burst
    length, is a theorem of arithmetic and requires no new machine axiom. -/
private theorem shift_power_128 (n : Nat) (hn : 7 ≤ n) :
    2^(n+2) = 128*2^(n-5) := by
  have hs : n+2 = 7+(n-5) := by omega
  have hpow : (2:Nat)^(n+2) = (2:Nat)^7 * 2^(n-5) := by
    rw [hs,Nat.pow_add]
  have h128 : (2:Nat)^7 = 128 := by decide
  simpa only [h128] using hpow

/-- The branch-13 large last-reset equation itself forces the affine q
    relation used by the all-time source-root theorem. No assumption of
    this relation is left in the public final classification. -/
theorem branch13_n_form_forces_q (n k q : Nat)
    (hn : n=63+128*k)
    (hreset : 4*(32*q+13)+3*n+15=3*2^(n+2)) :
    q+(3*k+2)=3*2^(n-5) := by
  have hlarge : 7 ≤ n := by omega
  have hp := shift_power_128 n hlarge
  have hh := hreset
  rw [hp] at hh
  omega

/-- Complete n-parametric necessary-condition theorem for all authentic
    13-family candidate last resets. The exact formula n=63+128*k
    is the family equation in the existing source reduction. -/
theorem branch13_k_mod16 (n k q : Nat)
    (hn : n=63+128*k)
    (hreset : 4*(32*q+13)+3*n+15=3*2^(n+2))
    (hr : Reach (32*q+13) (64*q+23)) :
    k%16=6 ∨ k%16=11 ∨ k%16=14 := by
  have hlarge : 18 ≤ n := by omega
  have hparam := branch13_n_form_forces_q n k q hn hreset
  exact BB429LastResetImproved.source_branch13_k_mod16_necessary
    n k q hlarge hreset hparam hr

theorem branch15_n_form_forces_q (n k q : Nat)
    (hn : n=103+128*k)
    (hreset : 4*(32*q+15)+3*n+15=3*2^(n+2)) :
    q+(3*k+3)=3*2^(n-5) := by
  have hlarge : 7 ≤ n := by omega
  have hp := shift_power_128 n hlarge
  have hh := hreset
  rw [hp] at hh
  omega

/-- Entire 15-family parameter classes k=0,1,4(mod8) excluded directly
    from the exact source last-reset equation and rooted orbit. -/
theorem branch15_k_mod8 (n k q : Nat)
    (hn : n=103+128*k)
    (hreset : 4*(32*q+15)+3*n+15=3*2^(n+2))
    (hr : Reach (32*q+15) (64*q+27)) :
    k%8=2 ∨ k%8=3 ∨ k%8=5 ∨ k%8=6 ∨ k%8=7 := by
  have hlarge : 18 ≤ n := by omega
  have hparam := branch15_n_form_forces_q n k q hn hreset
  exact BB429LastResetImproved.source_branch15_k_mod8_necessary
    n k q hlarge hreset hparam hr

#print axioms branch13_k_mod16
#print axioms branch15_k_mod8
end BB429LastResetParamClosed
