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

/-- Exact scalar Q-mass identity with all small authentic initial constants
    evaluated by kernel arithmetic; no 32750-step numeric replay. -/
theorem firstSecondaryQNumeric :
    qSum (sIter 32750 (2047,3071,firstPrimary)).2.2 +
      2^((lifeIter 32750 firstLives).length+2) =
      9293834+4*lifeLengthSum 32750 firstLives := by
  have h := firstSecondaryQScalar
  have hinit : qSum firstPrimary=9325560 := by decide
  have hpow : 2^firstPrimary.length=1024 := by decide
  rw [hinit,hpow] at h
  omega

/-- Complete authentic secondary-zero primary-prefix mass as a scalar
    lifetime-only expression, with all initial values kernel-evaluated. -/
theorem firstSecondaryPrefixNumeric :
    let e := sIter 32750 (2047,3071,firstPrimary)
    prefixMass e.1 e.2.1 e.2.2 =
      21952504+4*2^((lifeIter 32750 firstLives).length+2)+
        6*lifeLengthSum 32750 firstLives := by
  have h := BB6Coverage.Agent41F421.EpochWords.firstSecondaryMassTelescoping
  have hl := firstSecondaryCells
  have hs := firstLengthSum
  rcases he : sIter 32750 (2047,3071,firstPrimary) with ⟨a,b,ds⟩
  rw [he] at h hl
  simp only [Prod.fst,Prod.snd] at h hl
  rw [hs,hl] at h
  have hinit : prefixMass 2047 3071 firstPrimary=21923850 := by decide
  have hpow : 2^firstPrimary.length=1024 := by decide
  rw [hinit,hpow] at h
  simp only [he,Prod.fst,Prod.snd]
  omega

/-- The weighted mass of the single final lifetime list replaces the
    entire 32750-term history of cell-count powers. -/
theorem firstLifeMoment :
    lifeLengthSum 32750 firstLives +1446908 =
      4*mass (lifeIter 32750 firstLives) := by
  have h := lengthSumMass 32750 firstLives
    (by simp [Positive,firstLives])
  have hi : mass firstLives=328977 := by decide
  rw [hi] at h
  omega

/-- Pure endpoint scalar Q-mass law: only final lifetime length and mass. -/
theorem firstSecondaryQMoment :
    qSum (sIter 32750 (2047,3071,firstPrimary)).2.2 +
      2^((lifeIter 32750 firstLives).length+2) =
      3506202+16*mass (lifeIter 32750 firstLives) := by
  have hq := firstSecondaryQNumeric
  have hm := firstLifeMoment
  omega

/-- Exact blank-linked secondary-zero primary-prefix mass, expressed in
    closed form using only the final normalized P lifetime word. -/
theorem firstSecondaryPrefixMoment :
    let e := sIter 32750 (2047,3071,firstPrimary)
    prefixMass e.1 e.2.1 e.2.2 =
      13271056+4*2^((lifeIter 32750 firstLives).length+2)+
        24*mass (lifeIter 32750 firstLives) := by
  have h := firstSecondaryPrefixNumeric
  have hm := firstLifeMoment
  omega

#print axioms firstSecondaryCells
#print axioms firstSecondaryQScalar
#print axioms firstSecondaryHeadScalar
#print axioms firstSecondaryQNumeric
#print axioms firstSecondaryPrefixNumeric
#print axioms firstLifeMoment
#print axioms firstSecondaryQMoment
#print axioms firstSecondaryPrefixMoment
end F421SecondaryLifetimes
