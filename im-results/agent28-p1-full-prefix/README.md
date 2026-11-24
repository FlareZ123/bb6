# Endpoint-independent full-P carry prefix for P1

Status: the original prefix theorem and its carry automaton compile in Lean 4.36.0-rc2 via the existing manual Agent43 wall-telescoping workflow (run **45362274804**, success). This is an intermediate research result, not a BB(6) solution or a machine-halting conclusion. The new exact-endpoint transport below has locally compiled arithmetic and carry-block lemmas; its unchanged-source wrapper is awaiting focused compilation.

## Main theorem

See [`FullPrefix.lean`](FullPrefix.lean).

For every original-source history
```lean
CountCone (14*2^n - 2*n - 16) 3 b d m z
```
with `14 ≤ n`, and every `K` with `0 < K ≤ m`, the theorem
`BB6.Agent28FullPrefix.source_full_prefix` produces a Boolean list `xs` of length `K` satisfying
```lean
fullSumBits (7*2^n-(n+3)) 0 xs % 2^K = 2^K-1
```
Equivalently,
[
\sum_{s=0}^{K-1}x_s\bigl(7\cdot2^n-(n+3)-s\bigr)2^s\equiv -1\pmod{2^K}.
]

The theorem `source_countcone_cost_lt_full` is the corresponding obstruction: if the Boolean-prefix condition has no witness at layer `K`, then every original `CountCone` history has total cost `m<K`. It applies to **every endpoint**, not just the exceptional right-five endpoint.

## Why this is stronger than the existing short-prefix theorem

The existing `source_countcone_cost_lt` discards the `7*2^n` term modulo `2^K`, which requires `K≤n`. The new argument keeps that term and only requires `K≤m`.

**Scope clarification:** Agent43 had already source-lifted an endpoint-independent cost-side prefix for the range K≤n and K≤m. The new contribution is not endpoint independence by itself; it is retaining the full 7P term to extend the source prefix to every K≤m, including K>n.

The source `CostWitness` identity gives, for a duplicate-free list of edge-start costs `A`,
[
2+14P\sum_{s\in A}2^s
=2^m(d-1)+2\sum_{s\in A}(n+3+s)2^s,
\qquad P=2^n.
]
Since `d` is odd, writing `v=(d-1)/2` and rearranging gives
[
1+\sum_{s\in A}\bigl(7P-(n+3)-s\bigr)2^s=2^m v.
]
The source mass invariant shows `m≤Q=7P-(n+3)`, so every coefficient `Q-s` is a natural number. Truncating at any `K≤m` leaves the claimed residue `-1 mod 2^K`.

## Carry automaton

`fullCarryStates Q 0 [1] K` tracks all Boolean choices for
[
1+\sum_{s<K}x_s(Q-s)2^s
]
to be divisible by `2^K`. At position `j`, a carry `c` has:
- an omit transition to `c/2` when `c` is even;
- a select transition to `(c+Q-j)/2` when `c+Q-j` is even.

An empty layer at `K` therefore proves `m<K` for every source history. The initial carry is 1; when `Q` is odd this forces `x₀=1`, matching the source fact `0∈A`.

## Exact endpoint transport and direct right-five test

[ExactEndpoint.lean](ExactEndpoint.lean) gives a stronger source-level interface. Set (v=(d-1)/2) and (Q=7\cdot2^n-(n+3)). A genuine inverseAt edge of depth (t), starting at cumulative cost (m), satisfies the exact equation
[
v+(Q-m)=2^{t+1}v'.
]
It therefore corresponds to one selected bit followed by exactly (t) omitted bits. Induction on the genuine CountCone history yields the candidate theorem
```lean
(d-1)/2 ∈ fullCarryStates (7*2^n-(n+3)) 0 [1] m
```
with no additional endpoint, cost, or depth restriction. The proof uses the original inverseAt power equation and conserved mass, rather than a simulator or heuristic.

For d=5 the required carry is exactly **2**. Thus one finite certificate excluding carry 2 from each layer before an empty layer would close the whole critical right-five gate for that index, bypassing both high-reset and shifted-wall branches. The generic carry-block lemmas and source-equation arithmetic compiled locally with Lean 4.36.0-rc2 and ordinary axioms only against the exact copied carry definitions. The unchanged-source wrapper and concrete six-index certificates are not yet accepted. Agent43 is investigating the latter; the two agents are coordinating this direct test.

## Connection to the six finite full-wall carry survivors

The existing experimental `WallFullDPTo10000.js` scan reports full-P empty layers at:
```
n=30:   K=82
n=286:  K=1442
n=350:  K=586
n=1614: K=5824
n=2990: K=6154
n=3342: K=13730
```
The new Lean theorem means that any one of these empty-layer certificates, once formalized, excludes **all** `CountCone` histories of cost at least that `K`, regardless of endpoint. In the high-reset branch of the existing right-five dichotomy, `3*2^n ≤ (2*n+3)*z` and the positive-reset cost floor `m≥2z` give
[
m\ge 2z\ge\frac{6\cdot2^n}{2n+3}.
]
For each of the six listed indices this lower bound exceeds its listed empty layer, so a formal empty-layer certificate would eliminate that high-reset branch.

This is a proposed application, not yet a completed exclusion: the six concrete empty-layer certificates are still experimental JavaScript output, not Lean theorems. The low-reset branch remains a wall-specific exact-target problem and must be closed separately.

## Reproduction

The existing manual workflow `.github/workflows/agent43-p1-wall-telescoping.yml` now compiles `WallListSource.olean` and then `FullPrefix.lean`. Run 45362274804 compiled the new module successfully. The Lean file includes `#print axioms` audits for all new definitions/theorems; no `sorry` or new axiom is introduced here.

## Next useful step

Accept the exact endpoint source wrapper, and formalize six full-P certificates excluding carry 2 up to each empty layer. This direct endpoint test supersedes the need to certify the two branches separately if successful. The existing wall and prefix proofs remain useful for unbounded parameter classes. Do not promote the JS scan itself to a theorem.
