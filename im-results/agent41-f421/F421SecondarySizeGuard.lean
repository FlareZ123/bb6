import F421SecondarySize
import F421SecondaryQGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421SecondaryLifetimes

/-- Exact source-machine secondary primary-word length law, in two-symbol
    pairs. It covers arbitrary guarded terminal P-cell deletions and Q merges.
    The surviving cell count affects only D = 2^(new body length-1). -/
theorem secondaryPrefixGrowth (k a b : Nat) (cs : List PC)
    (hg : sPrimary (k+1) a b cs) :
    let (a',b',ys) := sNext b cs
    prefixMass a' b' ys = prefixMass a b cs + 2*2^cs.length+
      8*2^(drain 0 0 (dec cs)).1.length+1 := by
  have hP := secondaryPsumGuarded k b cs hg.2.2.1
  have hQ := secondaryQMassGuarded k a b cs hg
  have hlen := F421SecondaryLifetimes.drainLengthLe 0 0 (dec cs)
  have hlen' : (drain 0 0 (dec cs)).1.length≤cs.length := by
    simpa [dec] using hlen
  exact prefixMassIdentity a b cs hg.1 hP hQ hlen'

#print axioms secondaryPrefixGrowth
end BB6Coverage.Agent41F421.EpochWords
