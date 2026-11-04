import Lean.Elab.Tactic.Omega
import DObsSourceCandidate
import PaddedApplications
import CryptidTriplePairs

set_option maxHeartbeats 4000000
namespace BB6.Agent31RegularELow
open CryptidBoundary DRegularSource BB6.BoundaryPadding BB6.Padding

private theorem word_zero_pad (q : Nat) :
    oppairs q ++ [false,false] = false :: (pairs q ++ [false]) := by
  induction q with
  | zero => rfl
  | succ q ih =>
      simpa [oppairs, pairs, List.append_assoc] using
        (congrArg (fun zs : List Bool => false :: true :: zs) ih)

/-- E with no terminal unary suffix, including the pure-unary q=0 case. -/
theorem e_zero_suffix (k q : Nat) :
  ObsEq
    (run (12*k*k+49*k+50+4*q) (sourceSection ⟨3*k+4,q,0⟩))
    (sourceSection ⟨8*k+5,1,2*q+5⟩) := by
  let xs := List.replicate (3*k+2) true ++ oppairs q
  let n := 12*k*k+49*k+50+4*q
  have hpad := source_init_pad n 2 xs
  have hinput : init (xs ++ List.replicate 2 false) =
      init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ (false::[]))) := by
    simp only [xs, List.replicate_succ, List.replicate_zero,
      List.cons_append, List.append_assoc, List.append_nil]
    rw [word_zero_pad]
  have hx : run n (init (xs ++ List.replicate 2 false)) =
      (⟨[],false,List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true),5⟩ : Cfg) := by
    rw [hinput]
    simpa [n] using (full_E_pairs k q [])
  have hout : (⟨[],false,List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true),5⟩ : Cfg) =
      sourceSection ⟨8*k+5,1,2*q+5⟩ := by
    have hrep : List.replicate (8*k+5) true =
        true :: true :: List.replicate (8*k+3) true := by
      rw [show 8*k+5=(8*k+3)+1+1 by omega,
        List.replicate_succ, List.replicate_succ]
    have hp : List.replicate (2*q+6) true =
        true :: List.replicate (2*q+5) true := by
      rw [show 2*q+6=(2*q+5)+1 by omega, List.replicate_succ]
    simp only [sourceSection,init,oppairs,List.cons_append]
    rw [show 8*k+5-2=8*k+3 by omega, hrep, hp]
    simp [List.append_assoc]
  rw [hx, hout] at hpad
  simpa [n, sourceSection, xs] using hpad

#print axioms e_zero_suffix
end BB6.Agent31RegularELow
