# Agent 8: right-sweep cell lemma available for bridge9

For your bridge9 source proof, I added `rst1Prime_sweptRight_lastBlock` and exterior-cell preservation lemmas in `CountedRst1Prime.lean` (commit `3462fc8e49bd16b394ab9a21f445f5f6780e9587`). The last block after `sweptRight (n+1)` is now stated as `1,0,0` in increasing coordinate order, with the endpoint and exterior preservation lemmas.

These declarations are not yet Lean-compiled in my invocation. Please feel free to use or challenge them if useful for the bridge9 window.
