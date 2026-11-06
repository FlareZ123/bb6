import EZeroFirstChain

namespace BB6.Agent36EZeroFirst
open CryptidBoundary BB6.Agent36EZeroPairs0 BB6.Agent36PositiveFirst

set_option maxHeartbeats 100000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

def zTail (r : Nat) (ys : List Bool) : List Bool :=
  [true,true,false] ++ (pairs r ++ (false::ys))

def zEntry (k r : Nat) (ys : List Bool) : Cfg :=
  init (List.replicate (3*k+2) true ++ (false::zTail r ys))

def zOutput (k r : Nat) (ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (8*k+3) true ++
    (packetZero ++ (List.replicate (2*r) true ++ ys)),5⟩

/-- The q=0 E 110(10)^r0 word from the F/0 source has no earlier
    positive-time physical F/0 section, for every suffix and r,k. -/
theorem originalEZeroNoEarlier (k r : Nat) (ys : List Bool)
    (t : Nat) (hpos : 0<t)
    (ht : t<12*k*k+49*k+96+4*r) :
    ¬ PhysicalF0 (run t (zEntry k r ys)) := by
  let p : Nat := 12*k*k+41*k+33
  have hprefix : run p (zEntry k r ys) = ePairZero (4*k) r ys := by
    dsimp [p,zEntry,zTail]
    rw [prefix_E]
    rfl
  by_cases hbefore : t<p
  · have hf : (run t (zEntry k r ys)).st ≠ 5 :=
      BB6.CryptidPrefixFirstReturn.prefixE_positive_noF
        k (zTail r ys) t hpos hbefore
    intro hp
    exact hf hp.1
  · have hsplit : t = p+(t-p) := by omega
    rw [hsplit,run_add,hprefix]
    exact eZeroBoundaryNoPhysical (4*k) r ys (t-p)
      (by dsimp [p] at *; omega)

/-- For all natural k,r and arbitrary finite y, exact first positive
    physical F/0 return for 0 110(10)^r0, including its full output tape. -/
theorem originalEZeroFirst (k r : Nat) (ys : List Bool) :
    run (12*k*k+49*k+96+4*r) (zEntry k r ys) =
      zOutput k r ys
    ∧ (∀ t : Nat, 0<t → t<12*k*k+49*k+96+4*r →
        ¬ PhysicalF0 (run t (zEntry k r ys))) := by
  constructor
  · exact full_E_110_pairs_zero k r ys
  · intro t hpos ht
    exact originalEZeroNoEarlier k r ys t hpos ht

#print axioms originalEZeroNoEarlier
#print axioms originalEZeroFirst
end BB6.Agent36EZeroFirst
