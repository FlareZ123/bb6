import Lean.Elab.Tactic.Omega
import EOnePairTwoReturnsPolynomial
import BoundaryPadding

namespace BB6.Agent26EOnePair

open CryptidBoundary
open BB6.BoundaryPadding
open BB6.Agent26EFour

set_option maxHeartbeats 10000000
set_option linter.unusedSimpArgs false

private theorem padded_input (k : Nat) :
    (List.replicate (3*k+2) true ++ [false,true,true]) ++
        List.replicate 3 false =
    List.replicate (3*k+2) true ++
      false :: ([true,true,false,false,false] ++ ([] : List Bool)) := by
  simp [List.append_assoc]

/-- The implicit-blank source has the same physical second F/0 endpoint
    as the exact syntactically padded exceptional source. -/
theorem onepair_A_physical (t : Nat) :
    ObsEq
      (run (876*t*t+731*t+223)
        (init (List.replicate (3*(3*t)+2) true ++ [false,true,true])))
      (⟨[],false,List.replicate (64*t+27) true,5⟩ : Cfg) := by
  have hp := source_init_pad (876*t*t+731*t+223) 3
    (List.replicate (3*(3*t)+2) true ++ [false,true,true])
  rw [padded_input, e_two_A_polynomial t ([] : List Bool)] at hp
  simpa only [List.append_nil] using hp

theorem onepair_B_physical (t : Nat) :
    ObsEq
      (run (876*t*t+1187*t+452)
        (init (List.replicate (3*(3*t+1)+2) true ++ [false,true,true])))
      (⟨[],false,List.replicate (64*t+33) true ++
         (afterFirst ++ [false]),5⟩ : Cfg) := by
  have hp := source_init_pad (876*t*t+1187*t+452) 3
    (List.replicate (3*(3*t+1)+2) true ++ [false,true,true])
  rw [padded_input, e_two_B_polynomial t ([] : List Bool)] at hp
  exact hp

theorem onepair_E_physical (t : Nat) :
    ObsEq
      (run (876*t*t+1643*t+845)
        (init (List.replicate (3*(3*t+2)+2) true ++ [false,true,true])))
      (⟨[],false,List.replicate (64*t+49) true ++
         (sixPairsZero ++ [false]),5⟩ : Cfg) := by
  have hp := source_init_pad (876*t*t+1643*t+845) 3
    (List.replicate (3*(3*t+2)+2) true ++ [false,true,true])
  rw [padded_input, e_two_E_polynomial t ([] : List Bool)] at hp
  exact hp

#print axioms onepair_A_physical
#print axioms onepair_B_physical
#print axioms onepair_E_physical

end BB6.Agent26EOnePair
