import Lean.Elab.Tactic.Omega
import DObsSourceCandidate
import CryptidTriplePairs
import BoundaryPadding

set_option maxHeartbeats 3000000
namespace BB6.Agent31RegularETwo
open CryptidBoundary DRegularSource BB6.BoundaryPadding BB6.Padding

private theorem word_two (q : Nat) :
    oppairs (q+1) ++ [true,true] =
      false :: (pairs q ++ [true,true,true]) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simpa [oppairs, pairs, List.append_assoc] using
        congrArg (List.cons false ∘ List.cons true) ih

/-- E with two terminal ones, and at least one alternating pair, sends a
    terminal literal zero to the blank-right quotient, not to literal equality. -/
theorem e_two_suffix (k q : Nat) :
    ObsEq
      (run (12*k*k+49*k+58+6*q)
        (sourceSection ⟨3*k+4,q+1,2⟩))
      (sourceSection ⟨8*k+9,q+2,0⟩) := by
  let xs := List.replicate (8*k+7) true ++ oppairs (q+2)
  have hinput :
      sourceSection ⟨3*k+4,q+1,2⟩ =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ ([true,true,true] ++ []))) := by
    simp only [sourceSection, List.replicate_succ, List.replicate_zero,
      List.append_nil, List.cons_append]
    rw [show 3*k+4-2=3*k+2 by omega]
    simp only [init, List.append_assoc]
    rw [word_two]
    rfl
  have hfull := full_E_triple_pairs k q []
  have hrep : List.replicate (8*k+9) true =
      true :: true :: List.replicate (8*k+7) true := by
    rw [show 8*k+9=(8*k+7)+1+1 by omega,
      List.replicate_succ, List.replicate_succ]
  have hout :
      (⟨[],false,List.replicate (8*k+9) true ++
        (oppairs (q+2) ++ [false]),5⟩ : Cfg) =
      init (xs ++ [false]) := by
    simp only [xs, init, List.cons_append]
    rw [hrep]
    simp [List.append_assoc]
  have hpad : ObsEq (init xs) (init (xs ++ [false])) := by
    simpa using (source_init_pad 0 1 xs)
  have hsym : ObsEq (init (xs ++ [false])) (init xs) :=
    cfgEq_symm hpad
  rw [hinput, hfull, hout]
  simpa [sourceSection, xs] using hsym

#print axioms e_two_suffix
end BB6.Agent31RegularETwo
