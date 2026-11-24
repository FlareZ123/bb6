# Exact primitive-transition accounting for Sheep

The literal six-state machine 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE is formalized with finite tape lists and implicit infinite blanks. The indexed Trace relation checks each transition, including all sweeps and the initial blank prefix. Score counts successful moves plus the final undefined transition query.

## Exact theorem

```lean
theorem blank_score_iff (s : Nat) :
    Score s blank ↔ ∃ a c, WPath c 5 (2^a*4) ∧ s=12+c+powerLive a
```

The raw machine enters section 5 in 11 live moves. For P(m,k) = 0^∞1^m E> 1 1^k 0^∞, the exact live costs are:

| Source | Live cost |
|---|---|
| P(0,0) | 7 |
| P(0,k+1) | 5 |
| P(1,k) | 8 (then one halt query) |
| P(2m+2,k) | (4m+7)k+6m²+21m+14 |
| P(2m+3,k) | 2m²+11m+16 |

For t=2^a u, u odd ≥5, the next section is t+a+(u-1)/2 with cost C satisfying
6C = 4t²+12tu-24t+12(u-1)a-7u²+9u-24.
For u=3, next is t+a+3, and 3C+15=2t²+18t+24a.
For terminal t=2^j, j≥2, the live cost plus halt query satisfies
3C+3t=2t²+3j+1.

The exact score iff is proved by strong induction on the real live halt count, using deterministic stripping of indexed macro traces, not just forward simulation. No terminal path from 5 is established.

## Reproduction

Run python reconstruct.py; then lean SheepCounted.lean using Lean 4.36.0-rc2, import Std only. Local compiler succeeded; final blank_score_iff depends on propext and Quot.sound. No sorry or native_decide. This independent literal-table semantics is not yet imported into the upstream BusyBeaver library. Upstream uncounted source: google-deepmind/cryptids revision ced8f9f44f67a167d5ecc03e687b048c67926371, Sheep machine module.

Intermediate result: exact score reduction, no new attained lower bound or whole-machine decision.
