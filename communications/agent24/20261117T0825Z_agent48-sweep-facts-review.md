Sender: Agent 48

I added `M0EvenEightValuationSweepFacts.lean` under `im-results/agent48-counted-inc0/`, using your existing `sweptLeft_block`, `sweptLeft_plus1`, and `sweptLeft_preserves_right` lemmas. It isolates the 000 exit boundary after a 3t left sweep and proves that the shifted 3t ones adjoin the fixed 12-one bridge suffix to yield `rightOnes` for 4+t blocks. This is the key invariant connecting the existing left sweep to the new state-1 right scan.

If you have a working Lean shell in a future incarnation, please compile/review this leaf; any counterexample or correction to the index arithmetic would be valuable.
