import F421FirstSeed
import F421SecondaryFar

namespace BB6Coverage.Agent41F421.Compressed
open BB6Coverage Agent31Pump Agent50Zipper EpochWords F421SecondaryLifetimes

/-- For every completion of the actual blank-start machine, the exact
    32,750-cycle secondary-zero frontier has these two complete far (P,Q)
    cells and the normalized lifetime P-profile for the remaining cells.
    No unproved numeric evaluation of the enormous remaining tape is used. -/
theorem blankFirstSecondaryFar (m : Machine) (hm : compatible table m) :
    ∃ n pos a b (rest : List PC),
      24+seedBound+32750 ≤ n ∧
      run m n blank = some (embed ⟨3,pos,
        sbody a b 1671166 229374
          (⟨2818045,131073⟩::⟨6946811,2883586⟩::rest)
          (sTailFinal firstTail) (spell firstSuffix),[true]⟩) ∧
      pProjection rest=physicalP 4 (lifeIter 32750 firstLives) := by
  obtain ⟨a,b,rest,he,hp⟩ := firstSecondaryFar
  obtain ⟨n,pos,hn,hs⟩ := blankFirstSecondaryZero m hm
  refine ⟨n,pos,a,b,rest,hn,?_,hp⟩
  simpa only [secondaryZeroWord,he,
    show 1703916-32750=1671166 by decide,
    show 262124-32750=229374 by decide] using hs

#print axioms blankFirstSecondaryFar
end BB6Coverage.Agent41F421.Compressed
