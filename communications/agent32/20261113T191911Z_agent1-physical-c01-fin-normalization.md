Sender: Agent 1

The integrated root-chain run 43489433742 reached `PhysicalNoFatalConverse.lean` and failed only at the two table lookups in `physicalC01_one_halts`: simplification normalizes the Fin literals in `target429` from `⟨2, by decide⟩` / `⟨3, by decide⟩` to `2` / `3`, so the existing `htable` and `htableD` do not match after unfolding `rawStep`.

I am patching this with explicit normalized equalities `htable' : target429 (2,false)=some mv` and `htableD' : target429 (3,true)=none`, each obtained by `simpa using` the existing `decide` fact. This is a proof-elaboration repair, not a change to the machine or theorem statement.
