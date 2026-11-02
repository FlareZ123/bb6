# Agent 1: complete positive-output inversion of P1's recursive G

**Status:** exact, kernel-checked arithmetic infrastructure for the existing DeepMind-certified P1 acceleration. No BB(6) holdout decision or improved bound.

## Exact theorem

In `GInverse.lean` (imports the repository's `GParity.lean`), the new inductive relation `GAncestor b d k c` describes *every* input `(k,c)` such that the published recursive drain satisfies `G k c = (b,d)`, provided `b>0`.

- Terminal generator: `(b,d)=(4k+4,d)` has the unique direct high-branch input `(k,d+2k+2)`.
- Inverse recursion: from input `(k,2c+3)`, generate input `(k+⌊c/2⌋+1,c)`.

Lean proves **both** `GAncestor_sound` and `GAncestor_complete` for all natural parameters, with the only extra hypothesis `0<b` on completeness. Local compilation used Lean 4.36.0-rc2, returned no errors or `sorryAx`; `#print axioms` reported `[propext, Quot.sound]` for soundness and `[propext, Classical.choice, Quot.sound]` for completeness. All code is pure arithmetic and **does not** establish machine-to-counter correctness, which rests on the upstream Google DeepMind formalization.

`g_inverse.py` directly enumerates this finite inverse chain: start at `k=b/4-1, c=d+2k+2`, repeatedly replace `(k,c)` by `(k+⌊((c-3)/2)/2⌋+1,(c-3)/2)` while `c≥3` is odd. For `b>0`, output `b` must be divisible by four; the chain terminates because `c` strictly decreases. The list is mathematically characterized by the formal inductive relation; the Python implementation's correspondence to that relation is reviewed algebraically, **not itself formally verified by Lean**.

## Checks and target application

A local Python test checked 89,353 input pairs `0≤k,c<300` whose `G` output has positive first coordinate. Every original input appeared in the computed inverse list, and every generated candidate mapped back to the same output. This is finite consistency evidence complementing the universal Lean proof.

For the P1 halting-critical resets `(2,d_n)`, `d_n = 14·2^n - 2n - 10`, the already-established backward reduction requires the odd-sector gateway `(d_n-6,3)` for all `n≥2`. The new enumerator exhaustively lists all `G` inputs to this gateway, including the still-open `n≡2 (mod 4)` indices. For example:

| n | Gateway | Complete G input list |
|---|---|---|
| 2 | (36,3) | (8,21), (13,9), (15,3), (16,0) |
| 6 | (868,3) | (216,437), (325,217), (379,107), (406,52) |
| 10 | (14300,3) | (3574,7153), (5362,3575), (6256,1786) |
| 14 | (229332,3) | (57332,114669), (85999,57333), (100332,28665), (107498,14331), (111081,7164) |

These are **G** input pairs; they must be translated through the exact T branch and tested for reachability before any exclusion claim. Some inverses do not correspond to a valid incoming T step, or contradict existing global modular/even-c normal-form constraints. At least one viable predecessor remains in each listed open case.

The width of this backward search appears governed by the 2-adic valuation of `7·2^n-n-2`, and for `n≥6`, `n≡2 (mod 4)`, this valuation equals `v₂(n+2)`. This last arithmetic observation is an **unformalized derivation**, not part of the compiled theorem. It suggests a finite logarithmic branching analysis for individual critical indices, but does not imply a global nonhalting proof.

## Research priority

Build a symbolic invariant on *actual blank-reachable odd-c hubs* capable of excluding every residual candidate after this complete inverse. The existing repo's `AllOddCritical.lean` and `AllFourCritical.lean` already cover odd n and multiples of four; avoid repeating those results. Focus exclusively on `n≡2 (mod 4)` or a separate unresolved holdout. Keep all work in `im-results/` unless it genuinely settles a frontier machine or establishes another independently publishable improvement.
