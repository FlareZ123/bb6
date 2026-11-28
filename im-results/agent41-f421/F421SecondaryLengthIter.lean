import F421SecondarySizeGuard
import F421SecondaryExact

namespace BB6Coverage.Agent41F421.EpochWords
open F421SecondaryLifetimes

/-- Source-level preservation of the mixed primary invariant for a single
    exact arithmetic secondary successor. -/
theorem sPrimaryOneStep (k a b : Nat) (cs : List PC)
    (hp : sPrimary (k+1) a b cs) :
    let (a',b',ds) := sNext b cs
    sPrimary k a' b' ds := by
  have h := secondaryPrimaryCycleExact k a b 4 3 cs [] []
     ⟨2,2,true⟩ [] hp (by decide) (by decide)
     (by decide) (by decide) (by decide)
  exact h.1

/-- An exact finite weighted sum of the growth of all source primary prefixes;
    it does not need to compute their huge Q coordinates. -/
def growthSum : Nat → Nat × Nat × List PC → Nat
  | 0,_ => 0
  | k+1, (_,b,cs) =>
      2*2^cs.length+8*2^(drain 0 0 (dec cs)).1.length+1+
        growthSum k (sNext b cs)

/-- Exact telescoping source prefix-mass identity across an entire secondary
    countdown, including arbitrary deletion and Q-merge phases. -/
theorem secondaryPrefixIteration (k a b : Nat) (cs : List PC)
    (hp : sPrimary k a b cs) :
    let (a',b',ds) := sIter k (a,b,cs)
    prefixMass a' b' ds = prefixMass a b cs + growthSum k (a,b,cs) := by
  induction k generalizing a b cs with
  | zero =>
    simp [sIter,growthSum]
  | succ k ih =>
    have hs := secondaryPrefixGrowth k a b cs hp
    have hg := sPrimaryOneStep k a b cs hp
    rcases he : sNext b cs with ⟨a1,b1,cs1⟩
    rw [he] at hs hg
    simp only [Prod.fst,Prod.snd] at hs hg
    have ht := ih a1 b1 cs1 hg
    simp only [sIter,growthSum,he,Prod.fst,Prod.snd] at ht ⊢
    omega

theorem firstSecondaryPrefixMass :
    let (a',b',ds) := sIter 32750 (2047,3071,firstPrimary)
    prefixMass a' b' ds =
      prefixMass 2047 3071 firstPrimary +
        growthSum 32750 (2047,3071,firstPrimary) :=
  secondaryPrefixIteration 32750 2047 3071 firstPrimary firstPrimaryGood

#print axioms sPrimaryOneStep
#print axioms secondaryPrefixIteration
#print axioms firstSecondaryPrefixMass
end BB6Coverage.Agent41F421.EpochWords
