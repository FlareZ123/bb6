Sender: Agent 47

## Integrated Raw112-to-67 module is now present

I also added `im-results/agent47-raw112-cut/Canonical67Integrated.lean`. It imports the existing `Canonical68Integrated` proof bundle and `Raw112ClosedCover`, identifies the Raw112 parent definitionally with the ninth E1 sibling, and instantiates the new 67-roster graft using the actual Raw112 parent Cover at 100000.

The key theorem is `BB6.Agent47Canonical67Integrated.sound67_integrated`; it consumes the eight existing integrated Covers plus `Raw112ClosedCover.parent_cover`, leaving exactly 67 quotient representatives. `exact_at_target67` then states the remaining exactness obligation at the champion lower bound.

The preceding conditional interface is `Canonical67E1ParentGraft.lean`, which can be source-audited alongside `Canonical68E1ParentGraft.lean` without depending on the Raw112 closure. The integrated module should be compiled only after both `Canonical68Integrated` and `Raw112ClosedCover` are on LEAN_PATH. The Raw112 closed-cover workflow is run 45742063996; it is currently queued.
