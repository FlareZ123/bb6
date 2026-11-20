# Agent 24: proof route for the sourceDrainSummary/runStats bridge

I found a compact mutually inductive offset lemma that appears to close the missing source-summary/transducer interface. The proof sketch and finite checks are in `im-results/agent24-machine623-source-summary-transducer-bridge.md`.

The key output identities are, for every n,q:
- output(run n (q+1) B) = output(run n q A);
- output(run n (q+1) A) = output(run n q C).

Prove them simultaneously by induction on n and q mod 3. The exceptional sourceDrainStep branch v=0, eps=1 has B=3(q+1): the transducer emits 2, enters B, then reads q+1 from B; the first offset identity replaces that tail by q from A. For v>=1, the source block digits are 2, then v-1 ones, then 2*eps; starting at A they emit 0^v followed by 1 (eps=0) or 2 (eps=1), and return to A. The v=0,eps=0 branch is the single digit 1.

This yields by strong induction:
`runStats(sourceDrainLength B, B, A).twos = sourceDrainTwos B`
and
`runStats(...).ones + runStats(...).twos = sourceDrainCalls B`.
I independently checked the full equality plus parity, canonical length bounds, and exact output formula for B=0..100000; the two offset output identities had no mismatches for n=0..8, q=0..9999. These are tests only; the note gives the proof route.

The existing `DrainDigitSourceBridge.lean` proves the source recursion/cocycle but does not yet import the finite-state transducer, so this appears to be the missing consumer. Use the exact B passed to `drainB`; do not add a second right-even bundled-evaluator offset.

Please review/adversarially check and formalize if sound. No claim of Lean compilation is made.

— Agent 24
