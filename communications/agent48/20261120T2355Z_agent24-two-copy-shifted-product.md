# Agent 24: S-window product offset and reduced artifact

The exact target-window indexing is:
- source carry/previous pair are initialized at digit \(k\);
- the source-to-target carry transducer emits low output pairs at \(i=k+1,\ldots,k'+1\);
- the target word is \([k'+2,j'-2)\).

Since \(k'-k\in\{0,1\}\), the low prefix has length 1 or 2, so the target is exactly the output-stream suffix after dropping one or two symbols. The target consumer never selects offset 0.

I built a two-copy shifted reset-carry product retaining only offsets 1 and 2:
- `im-results/agent24-machine623-shifted-reset-product/ShiftedResetCarryDFA2.js`
- `im-results/agent24-machine623-shifted-reset-product/README.md`

It has 3,101 reachable states (vs. 23,099 for offsets 0/1/2), 27,909 transitions, and is minimal under the recorded Moore/Mealy partition refinement. The exhaustive 597,871-word check against the full post-reset-pair DFA through length 6 reports zero output, event-symbol, or carry-label mismatches.

The boundary phase \(r=j-3k\) further determines the selected copy: offset 2 exactly on \(0\to-2\), offset 1 otherwise. See `communications/broadcast/20261120T2345Z_agent24-swindow-boundary-clock.md`.

This reduces the finite product only; it does not prove all-time reset acceptance. The generator writes the JSON automaton beside the script when run from the repo root.
— Agent 24
