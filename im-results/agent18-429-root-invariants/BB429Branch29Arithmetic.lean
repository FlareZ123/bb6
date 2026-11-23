import BB429Branch29Odd31
import Lean.Elab.Tactic.Omega

/-!
# Exact last-reset exponential arithmetic for #429 29-mod32 class

This separates the costly source-level connector from the lightweight,
purely local arithmetic theorem. Once any exact original-source orbit
is transferred to the local blank-root accelerator, the result applies
to all lengths n, not just observed traces.
-/

namespace BB429Branch29Arithmetic
open BB429Reset31
set_option maxHeartbeats 20000000
set_option maxRecDepth 30000

/-- A state on the 29-mod32 odd-reset feeder genuinely reached from
blank, together with the exact terminal-burst Diophantine equation,
forces the burst length n into twelve mod16384 classes.

This is necessary, not sufficient, for halting; no existence of any
last reset is asserted. -/
theorem local_branch29_burst_mod16384
    (q n : Nat) (hq : 21≤q) (hn : 18≤n)
    (hroot : Reach (32*q+29) (64*q+55))
    (heq : 128*q+3*n+131=3*2^(n+2)) :
    n%16384=16255 ∨ n%16384=4991 ∨ n%16384=10239 ∨
    n%16384=14335 ∨ n%16384=2943 ∨ n%16384=8191 ∨
    n%16384=13183 ∨ n%16384=2047 ∨ n%16384=1919 ∨
    n%16384=6143 ∨ n%16384=11135 ∨ n%16384=16383 := by
  have hqmod :=
    BB429Branch29Odd31.rooted_29_q_twelve_mod128 q hq hroot
  have hpow : 2^(n+2)=16384*2^(n-12) := by
    have hsplit : n+2=14+(n-12) := by omega
    rw [hsplit,pow_add]
    norm_num
  have hmod : (128*q+3*n+131)%16384=0 := by
    rw [heq,hpow]
    omega
  rcases hqmod with h2 | h10 | h15 | h47 | h58 | h63 |
       h74 | h79 | h82 | h111 | h122 | h127
  all_goals omega

#print axioms local_branch29_burst_mod16384
end BB429Branch29Arithmetic
