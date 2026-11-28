import F421AugmentedQ
import F421SecondaryQGuard

namespace BB6Coverage.Agent41F421.EpochWords
open F421SecondaryLifetimes
open F421TertiaryGuard (drain)

/-- On every authentic guarded F421 secondary primary state, augmenting
    each Q run by its positional power of two turns sNext into a pure
    ordered merge of terminally deleted rows plus an appended birth. -/
theorem sNextAugGuarded (k a b : Nat) (cs : List PC)
    (hg : sPrimary (k+1) a b cs) :
    augQ 1 ((sNext b cs).2.2) =
      (mergedAug 1 0 cs).1 ++
        [b+2^cs.length+(mergedAug 1 0 cs).2] := by
  rcases hg with ⟨ha,hb,hp,hq,hlen⟩
  have hcap := capPOfPGood k 1 cs (by decide) hp
  have hb' : 2^cs.length≤b+1 := by omega
  have hqa := F421TertiaryGuard.drainQ (dec cs) 1 1 1 0 0
    (by decide) (by decide) (decQBudget 1 1 cs hq)
  rcases he : drain 0 0 (dec cs) with ⟨ys,H,r⟩
  rw [he] at hqa
  have hq' : qAtLeast 1 ys := qAtLeastBudget 2 1 ys (by decide) hqa.1
  exact sNextAug b cs hcap (by rw [he]; exact hq') hb'

#print axioms sNextAugGuarded
end BB6Coverage.Agent41F421.EpochWords
