import F421SecondaryTelescopingGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421SecondaryLifetimes

/-- Exact total Q mass after a whole guarded source secondary countdown,
    in terms only of the history of P-cell counts and the initial Q sum.
    All enormous individual Q-run values have been eliminated. -/
theorem secondaryQSumTelescoping (k a b : Nat) (cs : List PC)
    (hg : sPrimary k a b cs) (hb : b=3*2^cs.length-1) :
    let (a',b',ds) := sIter k (a,b,cs)
    qSum ds+2^ds.length+k =
      qSum cs+2^cs.length+4*lengthSum k (a,b,cs) := by
  induction k generalizing a b cs with
  | zero =>
    simp [sIter,lengthSum]
  | succ k ih =>
    have hq := secondaryQMassGuarded k a b cs hg
    have hlen := F421SecondaryLifetimes.drainLengthLe 0 0 (dec cs)
    have hlen' : (drain 0 0 (dec cs)).1.length≤cs.length := by
      simpa [dec] using hlen
    have haff := qMassAffine b cs hb hq hlen'
    have hguard := sPrimaryOneStep k a b cs hg
    have hnext := (nextHeadExact b cs).2
    rcases he : sNext b cs with ⟨a1,b1,cs1⟩
    rw [he] at haff hguard hnext
    simp only [Prod.fst,Prod.snd] at haff hguard hnext
    have ht := ih a1 b1 cs1 hguard hnext
    rcases heIter : sIter k (a1,b1,cs1) with ⟨a2,b2,ds⟩
    rw [heIter] at ht
    simp only [Prod.fst,Prod.snd] at ht
    simp only [sIter,lengthSum,he,heIter,Prod.fst,Prod.snd]
    omega

/-- Original authentic 32750-cycle source Q mass, with no Q-run replay. -/
theorem firstSecondaryQSum :
    let (a',b',ds) := sIter 32750 (2047,3071,firstPrimary)
    qSum ds+2^ds.length+32750 =
      qSum firstPrimary+2^firstPrimary.length+
        4*lengthSum 32750 (2047,3071,firstPrimary) := by
  apply secondaryQSumTelescoping 32750 2047 3071 firstPrimary firstPrimaryGood
  decide

#print axioms secondaryQSumTelescoping
#print axioms firstSecondaryQSum
end BB6Coverage.Agent41F421.EpochWords
