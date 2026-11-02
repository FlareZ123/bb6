# Agent 5: exact parity-run acceleration for Machine B

**Classification:** intermediate arithmetic result. This does not determine a BB(6) holdout or improve the global Busy Beaver bound.

Machine: `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE`.

Agent 18 proved the upstream-source bridge and the exact halting criterion for its scalar map, `G(z)=3*(z/2)+4+5*(z%2)`: the raw blank machine halts iff some recursively sampled `G^[A(n)](0)` is even, with `A(0)=3` and `A(n+1)=G^[A(n)](0)+9-3*(G^[A(n)](0)%2)`.

## Mathematical statements proved in Lean

Set `x=z+8`. The equation `G(z)+8=(3*x+7*(x%2))/2` is an **exact conjugacy to the positive 3x+7 generalized Collatz map**, and `shift_iter` establishes its identity for every iterate.

For a starting `z≥0`, let `v₂(N)` be the largest `k` with `2^k | N` for positive `N`:

* When `z` is even, the entire maximal constant-even run has length `k=v₂(z+8)`, and `G^k(z)+8=3^k*(z+8)/2^k`; the endpoint is odd.
* When `z` is odd, the maximal constant-odd run has length `k=v₂(z+15)`, and `G^k(z)+15=3^k*(z+15)/2^k`; the endpoint is even.

All intermediate iterates `G^j(z)`, `0≤j<k`, retain the starting parity. This gives a jump exactly to the next parity change. In particular, `0→4→10→19→36` has initial even block length 3 and then odd block length 1.

The theorem `later_opposite` proves `∀ z n, ∃ m>n, (G^m(z))%2 ≠ (G^n(z))%2`. Every scalar orbit switches parity infinitely often. **The recursively sampled parity problem remains entirely open**, because sparse sampling can in principle miss all the intervening even values.

## Proof and computational evidence

* `BParityRuns.lean.xz.b64` is the full self-contained Lean 4.36.0-rc2 proof source compressed with xz and encoded as base64. Uncompressed SHA256: `7818c8a6b29b4f21773fa9364faad7d6485adcdad0e9fa308f136a2ef2d717fc`.
* `BParityRunsSource.lean` establishes a definitional equality to **Agent 18's exact unmodified** `OneDim.G` and `OneDim.iterG`, then transfers the all-time parity-switch result. Locally verified using a matching-signature import stub; original-source CI verification is pending.
* `.github/workflows/agent5-b-certified-prefix.yml` was extended to verify the original source bridge and this file, still **manual-only**.
* `verify_parity_runs.py` passed 5,000 deterministic random partial-iteration tests, 10,000 exhaustive parity-run tests, and independently recomputed `G^[227097](0)` to have parity 1, 132,847 bits and SHA256 `15d1bf0d327f41d76b4a47e6d5293cab98143a69ae12c70487be42a23f3593cc`, agreeing with the existing giant finite Lean certificate.

Lean local axiom audits for `shift_iter`, `even_block`, `odd_block`, and `later_opposite`: `[propext, Quot.sound]`, no `sorryAx`. This is a reusable arithmetic representation rather than an original claim to discover the known generalized Collatz transformation. See [Agent 18's source-connected reduction](../agent18-b-cycle/ONE-DIMENSIONAL.md) for the still-undecided machine semantics.


## Exact 2-adic finite parity coding, source-certified

A second source module `BParityCoding.lean.xz.b64` (uncompressed SHA256 `5d01059206dce41bdacd8ea45f517ea4659777c0cea219ac8c6b2adb2be4a67c`) proves `parity_gap` and `G_parity_gap`. For any two starting values whose positive difference is `2^k*m` with odd `m`, their first `k` parity observations agree; at exactly the `k`-th position they differ, and the numerical gap has become `3^k*m`. The same module proves `G_no_eventual_parity_period`: **every** natural-start G orbit has an eventually *aperiodic* parity word. The source transfer file `BParityCodingSource.lean` checks the exact original unchanged Agent18 map and proves `source_parity_gap` and `source_no_eventual_parity_period`.

A third module `BParityWords.lean.xz.b64` (uncompressed SHA256 `d31a748aa486f7fba3e1ac62b26f4a8e1368e73a6cd45040af3a48efc4cf9625`) proves:
```text
∀ k, ∀ binary parity word b of length k,
∃! z with z<2^k such that parity(G^j(z))=b_j for all j<k.
```
The certificates are `parity_prefix_exists`, `parity_prefix_unique`, and `parity_word_bijection`, all compiled locally with `[propext, Quot.sound]`, no `sorryAx`. They constitute the standard finite 2-adic parity-coding phenomenon specialized to this map. We make **no novelty claim for generic Collatz parity coding**.

**Independent CI:** [run 41492546809](https://github.com/FlareZ123/bb6/actions/runs/41492546809) passed the aperiodicity and original-source bridge; [run 41493062011](https://github.com/FlareZ123/bb6/actions/runs/41493062011) additionally compiled the finite-word bijection and all prior unmodified source imports. Both are manual-only and used Lean 4.36.0-rc2. An earlier [run 41492034088](https://github.com/FlareZ123/bb6/actions/runs/41492034088) initially failed due to a workflow-local `LEAN_PATH` configuration, which was fixed and reverified.

**Implication and limitation:** no fixed finite-period classification describes the entire scalar parity itinerary; the exceptional reset-sampling indices remain an open infinite-horizon problem. The finite 2-adic bijection is a toolkit for backward parity-cylinder searches. It supplies no bound on the first even sampled bit and cannot prove its existence or absence.
