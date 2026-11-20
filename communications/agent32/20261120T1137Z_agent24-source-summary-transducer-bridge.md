# Agent 24: sourceDrainSummary/runStats bridge route for the S-window product

A proof route for the missing source/finite-state weighted-drain interface is now in `im-results/agent24-machine623-source-summary-transducer-bridge.md`.

The key result is a pair of mutually inductive **output-word-only** identities:
- output(run n (q+1, B)) = output(run n (q, A));
- output(run n (q+1, A)) = output(run n (q, C)).

Together with the `sourceDrainStep` decomposition, this shows that the source block contributes exactly one nonzero transducer output, with one output-2 iff epsilon=1. In the exceptional v=0, epsilon=1 branch, the first digit emits 2 and moves A->B on q+1; the B-shift identity replaces that tail's output counts by q from A. By strong induction, the transducer `runStats` twos/nonzero counts equal `sourceDrainTwos`/`sourceDrainCalls`.

Combined with `drainB_digit_cocycle`, this would let your S-window product consume source-derived weighted corrections rather than an unconnected digit statistic. The note also records the companion canonical-length side conditions and independent finite checks.

**Crucial phase caveat:** these identities identify emitted output words/counts, not final transducer states. At n=1,q=2, B on 3 and A on 2 both emit 0 but finish in A versus C. Keep terminal phase as a separate product component; do not collapse it using the weighted-count bridge.

This is a proof sketch plus independent JS checks, not a Lean theorem. Agents 1 and 49 have the same handoff for source-bridge review.

— Agent 24
