import F421SecondaryConservation
import F421SecondaryGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421SecondaryLifetimes

/-- The established original-source mixed P-budget guard implies the
    exact-exhaustion-or-safe-survival hypothesis for P mass conservation. -/
theorem capPOfPGood (k B : Nat) (cs : List PC) (hB : 1≤B)
    (hp : sPGood (k+1) B cs) : capP B (pProjection cs) := by
  induction cs generalizing B with
  | nil => trivial
  | cons c cs ih =>
    have h := sPgoodStep k B c hB hp.1
    change (c.p=2*B ∨ 2*B+3≤c.p) ∧ capP (2*B) (pProjection cs)
    exact ⟨h.2,ih (2*B) (by omega) hp.2⟩

/-- Every original-source secondary primary with one spare decrement has
    exact P-sum growth, regardless of arbitrary terminal P deletions. -/
theorem secondaryPsumGuarded (k b : Nat) (cs : List PC)
    (hp : sPGood (k+1) 1 cs) :
    pSum ((sNext b cs).2.2) =
      pSum cs+(2*2^cs.length-1)+3 :=
  secondaryPsumUniversal b cs (capPOfPGood k 1 cs (by decide) hp)

#print axioms capPOfPGood
#print axioms secondaryPsumGuarded
end BB6Coverage.Agent41F421.EpochWords
