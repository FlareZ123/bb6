import BoundaryPadding
import CryptidPairs

namespace BB6.BoundaryPadding

/-- The source-verified E-pairs macro remains correct at an implicit
    infinite-blank suffix, without confusing unequal finite lists. -/
theorem full_E_pairs_implicit_blank (k q : Nat) :
  ObsEq
    (CryptidBoundary.run (12*k*k+49*k+50+4*q)
      (CryptidBoundary.init (List.replicate (3*k+2) true ++
        false :: CryptidBoundary.pairs q)))
    (⟨[], false, List.replicate (8*k+5) true ++
      (false :: List.replicate (2*q+6) true), 5⟩ : CryptidBoundary.Cfg) := by
  let xs := List.replicate (3*k+2) true ++ false :: CryptidBoundary.pairs q
  let t := 12*k*k+49*k+50+4*q
  have hp := source_init_pad t 1 xs
  have heq : CryptidBoundary.run t
        (CryptidBoundary.init (xs ++ [false])) =
      (⟨[], false, List.replicate (8*k+5) true ++
        (false :: List.replicate (2*q+6) true), 5⟩ : CryptidBoundary.Cfg) := by
    simpa [t, xs, List.append_assoc] using
      (CryptidBoundary.full_E_pairs k q [])
  simp only [List.replicate_one] at hp
  rw [heq] at hp
  simpa [t, xs] using hp

#print axioms full_E_pairs_implicit_blank
end BB6.BoundaryPadding
