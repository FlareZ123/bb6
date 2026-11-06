import Lean.Elab.Tactic.Omega
import EOnePairTwoReturnsBE

namespace BB6.Agent26EOnePair

open CryptidBoundary
open BB6.Agent26EFour

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

private theorem closeInc : CryptidA.wordInc fourCloseCode = 8 := by rfl
private theorem closeCost (m : Nat) :
    CryptidA.wordCost m fourCloseCode = 6*m+49 := by rfl

theorem e_two_A_polynomial (t : Nat) (ys : List Bool) :
    run (876*t*t+731*t+223)
      (init (List.replicate (3*(3*t)+2) true ++
        false :: ([true,true,false,false,false] ++ ys))) =
      ⟨[],false,List.replicate (64*t+27) true ++ ys,5⟩ := by
  have ht :
    (12*(3*t)*(3*t)+49*(3*t)+96)+
      ((12*(8*t)*(8*t)+41*(8*t)+32)+
        (CryptidA.wordCost (4*(8*t)+3) fourCloseCode +
          (2*((4*(8*t)+3)+CryptidA.wordInc fourCloseCode)+6))) =
    876*t*t+731*t+223 := by
    rw [closeCost,closeInc]
    have h3 : t*(3*t)=3*(t*t) := by ac_rfl
    have h8 : t*(8*t)=8*(t*t) := by ac_rfl
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8]
    omega
  have hn : 2*((4*(8*t)+3)+CryptidA.wordInc fourCloseCode)+5=64*t+27 := by
    rw [closeInc]
    omega
  rw [←ht]
  simpa only [←hn] using e_two_A t ys

theorem e_two_B_polynomial (t : Nat) (ys : List Bool) :
    run (876*t*t+1187*t+452)
      (init (List.replicate (3*(3*t+1)+2) true ++
        false :: ([true,true,false,false,false] ++ ys))) =
      ⟨[],false,List.replicate (64*t+33) true ++
        (afterFirst ++ false :: ys),5⟩ := by
  have ht :
    (12*(3*t+1)*(3*t+1)+49*(3*t+1)+96)+
      (12*(8*t+3)*(8*t+3)+49*(8*t+3)+40)=
    876*t*t+1187*t+452 := by
    have h3 : t*(3*t)=3*(t*t) := by ac_rfl
    have h8 : t*(8*t)=8*(t*t) := by ac_rfl
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8]
    omega
  have hn : 8*(8*t+3)+9 = 64*t+33 := by omega
  rw [←ht]
  simpa only [hn] using e_two_B t ys

theorem e_two_E_polynomial (t : Nat) (ys : List Bool) :
    run (876*t*t+1643*t+845)
      (init (List.replicate (3*(3*t+2)+2) true ++
        false :: ([true,true,false,false,false] ++ ys))) =
      ⟨[],false,List.replicate (64*t+49) true ++
        (sixPairsZero ++ false :: ys),5⟩ := by
  have ht :
    (12*(3*t+2)*(3*t+2)+49*(3*t+2)+96)+
      (12*(8*t+5)*(8*t+5)+49*(8*t+5)+58)=
    876*t*t+1643*t+845 := by
    have h3 : t*(3*t)=3*(t*t) := by ac_rfl
    have h8 : t*(8*t)=8*(t*t) := by ac_rfl
    simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc,h3,h8]
    omega
  have hn : 8*(8*t+5)+9=64*t+49 := by omega
  rw [←ht]
  simpa only [hn] using e_two_E t ys

#print axioms e_two_A_polynomial
#print axioms e_two_B_polynomial
#print axioms e_two_E_polynomial

end BB6.Agent26EOnePair
