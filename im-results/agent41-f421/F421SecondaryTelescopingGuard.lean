import F421SecondaryTelescoping
import F421SecondaryLengthIter

namespace BB6Coverage.Agent41F421.EpochWords
open F421SecondaryLifetimes

/-- The exact entire primary-prefix mass at each guarded source state is a
    positive affine function of the sum of powers of its cell counts. No
    expansion of individual Q-run integers is needed. -/
theorem secondaryMassTelescoping (k a b : Nat) (cs : List PC)
    (hp : sPrimary k a b cs) :
    let (a',b',ds) := sIter k (a,b,cs)
    prefixMass a' b' ds+4*2^cs.length =
      prefixMass a b cs+4*2^ds.length+
        6*lengthSum k (a,b,cs)+k := by
  induction k generalizing a b cs with
  | zero =>
    simp [sIter,lengthSum]
  | succ k ih =>
    have hs := secondaryPrefixGrowth k a b cs hp
    have hpw := nextLengthPower b cs
    have hg := sPrimaryOneStep k a b cs hp
    rcases he : sNext b cs with ⟨a1,b1,cs1⟩
    rw [he] at hs hpw hg
    simp only [Prod.fst,Prod.snd] at hs hpw hg
    have hAffine : prefixMass a1 b1 cs1+4*2^cs.length =
        prefixMass a b cs+4*2^cs1.length+6*2^cs.length+1 := by omega
    have ht := ih a1 b1 cs1 hg
    rcases heIter : sIter k (a1,b1,cs1) with ⟨a2,b2,ds⟩
    rw [heIter] at ht
    simp only [Prod.fst,Prod.snd] at ht
    simp only [sIter,lengthSum,he,heIter,Prod.fst,Prod.snd]
    omega

theorem firstSecondaryMassTelescoping :
    let (a',b',ds) := sIter 32750 (2047,3071,firstPrimary)
    prefixMass a' b' ds+4*2^firstPrimary.length =
      prefixMass 2047 3071 firstPrimary+4*2^ds.length+
        6*lengthSum 32750 (2047,3071,firstPrimary)+32750 :=
  secondaryMassTelescoping 32750 2047 3071 firstPrimary firstPrimaryGood

#print axioms secondaryMassTelescoping
#print axioms firstSecondaryMassTelescoping
end BB6Coverage.Agent41F421.EpochWords
