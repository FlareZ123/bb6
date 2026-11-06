import Lean.Elab.Tactic.Omega
import E1101010111ThenAFive

namespace BB6.Agent26EThenAFive

open CryptidBoundary
open BB6.Agent26E1101010111

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

theorem fiveInc (r : Nat) :
    CryptidA.wordInc (List.replicate r true ++ List.replicate 5 false) =
      4*r+5 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change 4 + CryptidA.wordInc
      (List.replicate r true ++ List.replicate 5 false) = 4*(r+1)+5
    rw [ih]
    omega

theorem fiveCost (m r : Nat) :
    CryptidA.wordCost m (List.replicate r true ++ List.replicate 5 false) =
      6*m*r+29*r+12*r*r+10 := by
  induction r generalizing m with
  | zero => rfl
  | succ r ih =>
    change 6*m+41 + CryptidA.wordCost (m+4)
      (List.replicate r true ++ List.replicate 5 false) =
      6*m*(r+1)+29*(r+1)+12*(r+1)*(r+1)+10
    rw [ih]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    omega

/-- Exact polynomial for the twice-returned original D-start machine,
    with the extra physical zero after the exceptional E packet. -/
theorem e_then_a_five_polynomial (t u : Nat) (ys : List Bool) :
    run (876*t*t+384*t*u+2411*t+48*u*u+554*u+1729)
      (init (List.replicate (9*t+8) true ++
        false :: (pairs (3*u+2) ++ wordE (false::ys)))) =
      ⟨[], false, List.replicate (64*t+16*u+93) true ++ ys,5⟩ := by
  have ht :
    (12*(3*t+2)*(3*t+2)+49*(3*t+2)+80+4*(3*u+2)) +
    ((12*(8*t+6)*(8*t+6)+41*(8*t+6)+32)+
      (CryptidA.wordCost (4*(8*t+6)+3) (fiveTokens u)+
      (2*((4*(8*t+6)+3)+CryptidA.wordInc (fiveTokens u))+6))) =
    876*t*t+384*t*u+2411*t+48*u*u+554*u+1729 := by
    unfold fiveTokens
    rw [fiveCost, fiveInc]
    have h3 : t*(3*t)=3*(t*t) := by ac_rfl
    have h8 : t*(8*t)=8*(t*t) := by ac_rfl
    have h2 : t*(2*u)=2*(t*u) := by ac_rfl
    have hu : u*(2*u)=2*(u*u) := by ac_rfl
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,h3,h8,h2,hu]
    omega
  have hn : 2*(4*(8*t+6)+3+CryptidA.wordInc (fiveTokens u))+5 =
      64*t+16*u+93 := by
    unfold fiveTokens
    rw [fiveInc]
    omega
  have hs := e_then_a_five t u ys
  dsimp at hs
  rw [←ht]
  simpa only [show 9*t+8 = 3*(3*t+2)+2 by omega, ←hn] using hs

#print axioms fiveInc
#print axioms fiveCost
#print axioms e_then_a_five_polynomial

end BB6.Agent26EThenAFive
