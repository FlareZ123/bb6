import EPositivePacket
namespace BB6.Agent36PositiveDoubleZero
open CryptidBoundary

/-- Arbitrary suffix and all natural k,q,r, with at least one leading pair. -/
theorem full_E_positive_double_zero_clean (k q r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+64+4*q+4*r)
      (init (List.replicate (3*k+2) true ++
        false :: (pairs (q+1) ++ ([true,true,false] ++
          (pairs r ++ (false::ys)))))) =
    ⟨[],false,List.replicate (8*k+5) true ++
      (false :: (List.replicate (2*q+4) true ++
        (false :: (List.replicate (2*r+6) true ++ ys)))),5⟩ := by
  simpa only [packetSimplified] using
    (full_E_positive_double_zero k q r ys)

#print axioms full_E_positive_double_zero_clean
end BB6.Agent36PositiveDoubleZero
