import F421SecondaryLifeCount
import F421SecondaryQTelescoping

namespace F421SecondaryLifetimes
open BB6Coverage.Agent41F421.EpochWords

/-- Entire authentic 32750-cycle primary cell count depends only on the
    normalized P lifetime recurrence; Q coordinates are immaterial. -/
theorem firstSecondaryCells :
    (sIter 32750 (2047,3071,firstPrimary)).2.2.length =
      (lifeIter 32750 firstLives).length+2 := by
  obtain ⟨a,b,hs,he,hr⟩ := firstSecondaryFar
  have hLen := congrArg List.length hr
  simp only [pProjection,List.length_map,physicalPLength] at hLen
  rw [he]
  simp only [Prod.fst,Prod.snd,List.length_cons]
  omega

/-- Exact total Q sum of all primary rows in the authentic blank-linked
    secondary-zero endpoint. The right side depends only on the small,
    positive lifetime recurrence, not on any huge individual Q-run integer. -/
theorem firstSecondaryQScalar :
    qSum (sIter 32750 (2047,3071,firstPrimary)).2.2 +
      2^((lifeIter 32750 firstLives).length+2)+32750 =
      qSum firstPrimary+2^firstPrimary.length+
        4*lifeLengthSum 32750 firstLives := by
  have hq := BB6Coverage.Agent41F421.EpochWords.firstSecondaryQSum
  have hl := firstSecondaryCells
  have hs := firstLengthSum
  rcases he : sIter 32750 (2047,3071,firstPrimary) with ⟨a,b,ds⟩
  rw [he] at hl hq
  simp only [Prod.fst,Prod.snd] at hl hq
  rw [hs] at hq
  rw [hl] at hq
  simpa only [he,Prod.fst,Prod.snd] using hq

/-- Exact source leading P/Q values for 32750 cycles, without numeric
    evaluation of the 8200-bit length-index exponent. -/
theorem firstSecondaryHeadScalar :
    (sIter 32750 (2047,3071,firstPrimary)).1 =
      2*2^((lifeIter 32750 firstLives).length+2)-1 ∧
    (sIter 32750 (2047,3071,firstPrimary)).2.1 =
      3*2^((lifeIter 32750 firstLives).length+2)-1 := by
  have h := iterHeadExact 32749 2047 3071 firstPrimary
  have hl := firstSecondaryCells
  rcases he : sIter 32750 (2047,3071,firstPrimary) with ⟨a,b,ds⟩
  rw [he] at h hl
  simp only [Prod.fst,Prod.snd] at h hl
  rw [hl] at h
  simpa only [he,Prod.fst,Prod.snd] using h

#print axioms firstSecondaryCells
#print axioms firstSecondaryQScalar
#print axioms firstSecondaryHeadScalar
end F421SecondaryLifetimes
