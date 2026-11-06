import EPositiveFirstBoundary
import PrefixNoF

namespace BB6.Agent36PositiveFirst
open CryptidBoundary BB6.Agent36PositiveDoubleZero

set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- From the actual original six-state F/0 entry, the exceptional E packet
    has no positive-time physical F/0 return before the stated quadratic time.
    This is uniform in every natural k,q,r and arbitrary right suffix ys. -/
theorem originalEPositiveNoEarlier
    (k q r : Nat) (ys : List Bool) (t : Nat)
    (hpos : 0 < t)
    (ht : t < 12*k*k+49*k+64+4*q+4*r) :
    ¬ PhysicalF0
      (run t (init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ ([true,true,false] ++
          (pairs r ++ (false::ys))))))) := by
  let xs : List Bool :=
    pairs (q+1) ++ ([true,true,false] ++ (pairs r ++ (false::ys)))
  let p : Nat := 12*k*k+41*k+33
  have hprefix : run p
      (init (List.replicate (3*k+2) true ++ false::xs)) =
      input (4*k+1) q r ys := by
    dsimp [p,xs]
    rw [prefix_E]
    rfl
  by_cases hbefore : t < p
  · have hf : (run t
        (init (List.replicate (3*k+2) true ++ false::xs))).st ≠ 5 :=
      BB6.CryptidPrefixFirstReturn.prefixE_positive_noF k xs
        t hpos hbefore
    intro hp
    exact hf hp.1
  · have hsplit : t = p+(t-p) := by omega
    change ¬ PhysicalF0 (run t
      (init (List.replicate (3*k+2) true ++ false::xs)))
    rw [hsplit, run_add, hprefix]
    exact ePositiveBoundaryNoPhysical (4*k+1) q r ys
      (t-p) (by dsimp [p] at *; omega)

/-- Exact universal first positive physical F/0 return, including the full
    right tape, from the six-state original D machine. -/
theorem originalEPositiveFirst (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*q+4*r)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ ([true,true,false] ++
          (pairs r ++ (false::ys))))))
      = ⟨[],false,List.replicate (8*k+5) true ++
          (false :: (List.replicate (2*q+4) true ++
            (false :: (List.replicate (2*r+6) true ++ ys)))),5⟩
    ∧ (∀ t : Nat, 0<t → t<12*k*k+49*k+64+4*q+4*r →
        ¬ PhysicalF0
          (run t (init (List.replicate (3*k+2) true ++
            false :: (pairs (q+1) ++ ([true,true,false] ++
              (pairs r ++ (false::ys))))))))) := by
  constructor
  · exact full_E_positive_double_zero_clean k q r ys
  · intro t hpos ht
    exact originalEPositiveNoEarlier k q r ys t hpos ht

#print axioms originalEPositiveNoEarlier
#print axioms originalEPositiveFirst
end BB6.Agent36PositiveFirst
