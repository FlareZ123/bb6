import Frontier429
import Lean.Elab.Tactic.Omega
namespace BB429RootPairNormalizer
open Frontier429

/-- Every two nearest-first `10` pairs to the left of E/0 become
    the four-cell word `1110` to its right in exactly six transitions. -/
private theorem e0_four (l r : List Bool) :
    run 6 ⟨4,[true,false,true,false] ++ l,false,r⟩ =
    some ⟨4,l,false,[true,true,true,false] ++ r⟩ := by rfl

private def inWords : Nat → List Bool
  | 0 => []
  | n+1 => [true,false,true,false] ++ inWords n

private def outWords : Nat → List Bool
  | 0 => []
  | n+1 => [true,true,true,false] ++ outWords n

private theorem outWords_tail (n : Nat) :
    outWords (n+1) = outWords n ++ [true,true,true,false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change [true,true,true,false] ++ outWords (n+1) =
      ([true,true,true,false] ++ outWords n) ++ [true,true,true,false]
    rw [ih, List.append_assoc]

/-- Unbounded exact left-to-right pair conversion, with arbitrary
    untouched left and right context; source-level six-step loop. -/
theorem e0_pair_normalize (n : Nat) (l r : List Bool) :
    run (6*n) ⟨4,inWords n ++ l,false,r⟩ =
    some ⟨4,l,false,outWords n ++ r⟩ := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [show 6*(n+1)=6+6*n by omega,run_add]
    simp only [inWords, List.append_assoc, e0_four, Option.bind_some]
    rw [ih]
    simp only [outWords_tail, List.append_assoc]

#print axioms e0_pair_normalize
end BB429RootPairNormalizer
