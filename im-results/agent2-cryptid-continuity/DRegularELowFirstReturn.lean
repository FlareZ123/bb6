import PairsFirstReturn

/-!
Strict first-return upgrade for the D-regular low-E row.

The source endpoint is already established by `CryptidBoundary.full_E_pairs`
and `DRegularELow.e_zero_suffix`.  This wrapper adds the missing no-earlier-F
fact: the E prefix has no F-state, and the remaining `ePairs` phase has the
strict `ePairs_first_return` certificate from `PairsFirstReturn`.
-/

namespace BB6.DRegularELowFirstReturn

open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidPairsFirstReturn
open BB6.CryptidE111FirstReturn

theorem full_E_pairs_first_return (k q : Nat) :
    run (12*k*k + 49*k + 50 + 4*q)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs q ++ [false]))) =
      ⟨[], false,
        List.replicate (8*k+5) true ++
          (false :: List.replicate (2*q+6) true), 5⟩ ∧
    ∀ t, 0 < t → t < 12*k*k + 49*k + 50 + 4*q →
      ¬ IsPhysicalReturn
        (run t (init (List.replicate (3*k+2) true ++
          false :: (pairs q ++ [false]))) := by
  constructor
  · simpa using (CryptidBoundary.full_E_pairs k q [])
  · intro t hpos ht hphys
    let prefix : Nat := 12*k*k + 41*k + 33
    let tail : Nat := 2*(4*k+1) + 4*q + 15
    by_cases hpref : t < prefix
    · exact (prefixE_positive_noF k (pairs q ++ [false]) t hpos hpref)
        hphys.1
    · have hdecomp : t = prefix + (t-prefix) := by omega
      have htail : t-prefix < tail := by
        dsimp [prefix, tail] at *
        omega
      rw [hdecomp, run_add, prefix_E] at hphys
      change IsPhysicalReturn
        (run (t-prefix) (ePairs (4*k+1) q [])) at hphys
      exact (ePairs_first_return (4*k+1) q []).2
        (t-prefix) htail hphys.1

#print axioms full_E_pairs_first_return

end BB6.DRegularELowFirstReturn
