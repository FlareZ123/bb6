# Machine C: original-source strict mass growth and a fixed-target reachability cutoff

**Research state (6 November 2026): source-certified structural results and an independent reproduction of an earlier single-gate exclusion. Machine C remains undecided.** [Full research note, detailed proof and verification history](FULL_RESEARCH_LOG.md).

## Verified results

For the original Machine C section map from authentic blank state `(5,1)`, mass is `a+2*k`. [PositiveMassOriginal.lean](PositiveMassOriginal.lean) and [ExactDeltaFour.lean](ExactDeltaFour.lean) classify the `+2` and `+4` mass increments for successful positive-right steps. [BlankMassFour.lean](BlankMassFour.lean) proves the authentic blank orbit always satisfies `7+4*n≤a+2*k` at section index `n`.

[OriginalFiniteReach.lean](OriginalFiniteReach.lean) derives an **exact fixed-target decider** by checking only `n≤(a+2*k-7)/4`. These original-source proofs passed [CI 41670293123](https://github.com/FlareZ123/bb6/actions/runs/41670293123), with standard axioms only.

The earlier 16-segment `m=8` all-time terminal-gate certificate passed [source CI 41670233031](https://github.com/FlareZ123/bb6/actions/runs/41670233031). This dossier's separate 147-chunk trace reproduces that already-known result, rather than proving a different excluded gate.

## Remaining problem

Existing work already supplies weaker fixed-target decidability. The improvement here is the sharper mass-growth cutoff. A **uniform** blank-origin restriction over the infinite low/high stopping families is still required. The finite decision for any chosen target does not decide the machine.

See the [full research log](FULL_RESEARCH_LOG.md) for all trace chunks, equations, prior-art comparison, reproduction instructions and precise original-source CI history.
