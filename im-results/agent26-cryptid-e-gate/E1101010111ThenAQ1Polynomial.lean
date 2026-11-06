import Lean.Elab.Tactic.Omega
import E1101010111ThenAQ1

namespace BB6.Agent26EThenAQ1

open CryptidBoundary
open BB6.Agent26E1101010111

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

/-- All-parameter closed primitive-step count for the guarded q=3u+1
    E-to-A two-return original D-start machine family. -/
theorem e_then_a_q1_polynomial (t u : Nat) (ys : List Bool) :
    run (876*t*t+384*t*u+2219*t+48*u*u+506*u+1472)
      (init (List.replicate (9*t+8) true ++
        false :: (pairs (3*u+1) ++ wordE (false::ys)))) =
      ⟨[], false, List.replicate (64*t+16*u+71) true ++
        (false :: List.replicate 14 true ++ ys),5⟩ := by
  have ht :
    (12*(3*t+2)*(3*t+2)+49*(3*t+2)+80+4*(3*u+1)) +
    ((12*(8*t+6)*(8*t+6)+41*(8*t+6)+32)+
      (CryptidA.wordCost (4*(8*t+6)+3) (tripleTokens u)+
        (2*((4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u))-1)+34))) =
      876*t*t+384*t*u+2219*t+48*u*u+506*u+1472 := by
    unfold tripleTokens
    rw [BB6.Agent26EThenA.tripleCost, BB6.Agent26EThenA.tripleInc]
    have hsub : (4*(8*t+6)+3+4*(2*u+2))-1 =
      4*(8*t+6)+2+4*(2*u+2) := by omega
    rw [hsub]
    have h3 : t*(3*t)=3*(t*t) := by ac_rfl
    have h8 : t*(8*t)=8*(t*t) := by ac_rfl
    have h2 : t*(2*u)=2*(t*u) := by ac_rfl
    have hu : u*(2*u)=2*(u*u) := by ac_rfl
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8,h2,hu]
    omega
  have hn :
      2*((4*(8*t+6)+3+CryptidA.wordInc (tripleTokens u))-1)+3 =
      64*t+16*u+71 := by
    unfold tripleTokens
    rw [BB6.Agent26EThenA.tripleInc]
    omega
  have hs := e_then_a_q1 t u ys
  dsimp at hs
  rw [←ht]
  simpa [show 9*t+8=3*(3*t+2)+2 by omega, ←hn] using hs

#print axioms e_then_a_q1_polynomial

end BB6.Agent26EThenAQ1
