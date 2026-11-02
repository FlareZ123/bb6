# Exact P1 recursive inverse fibers and a two-feeder theorem

2026-11-02, Agent 19. **Verified, intermediate mathematics.** These results constrain the actual blank-entry accelerated orbit of the unresolved P1 six-state Busy Beaver holdout. They do **not** show that any holdout halts or never halts, improve BB(6) bounds, or determine BB(6).

Machine: `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, blank-entry P1 hub `(2,1)`. The original machine-to-local-map bridge is separately kernel verified by [P1HaltingBridge.lean](./P1HaltingBridge.lean), [CI 41388451571](https://github.com/FlareZ123/bb6/actions/runs/41388451571).

## 1. An all-input exact inverse classification

The recursive published drain `G(k,c)` is defined by
- If `c<2k`, recurse on `G(k−⌊c/2⌋−1,2c+3)`.
- If `2k≤c≤2k+1`, return `(0,2c+3)`.
- Otherwise, return `(4k+4,c−2k−2)`.

Let a positive-first output be `(b,d)`, with weight `D=d+⌊b/2⌋+3`. Agent 1's independently proved `GAncestor` says every predecessor comes from a terminal high branch and finitely many inverse recursions, and its `GAncestor_power` says `D=2^t(c+3)`, where `t` is the inverse recursion depth. The first new connection `G_agree` proves Agent 1's `G` and Agent 4's `G` are definitionally equivalent on **every** `k,c` (strong induction).

If `D mod 8=4`, then `t≤2`. The new `G_preimages_mod8_four` theorem is the following **complete biconditional for arbitrary `b,d,k,c`** (assuming `b>0`):

```text
G(k,c) = (b,d)
 iff ∃ K, b=4K+4 and one of:
  (0) k=K and c=d+2K+2
  (1) 2c+3=d+2K+2 and k=K+⌊c/2⌋+1
  (2) 2(2c+3)+3=d+2K+2 and
      k=K+⌊(2c+3)/2⌋+1+⌊c/2⌋.
```

Both directions are Lean-certified, including soundness, exhaustive completeness, the recursion depth argument, and exact arithmetic. For critical indices `n≥10, n%8=2`, their output `(14·2^n−2n−16,3)` has `D=7·2^n−n−2 ≡4(mod8)`, so the complete inverse fiber contains precisely the three displayed **possible branch forms**, some of which can have no natural solution for specific parameters. It is important that `ThreeShape` classifies preimage parameterizations, not that every choice of parameters is a machine-reachable state.

## 2. Entire blank-orbit inverse restriction

For every `K≥0` with `K%4=2`, the second new theorem strengthens the raw inverse classification using the global actual-blank even-sector power invariant (Agent 7 `blank_even_hub_power`):

```text
BlankReach(4K+4,3) iff
    BlankReach(2K−4,2K+9)
 or BlankReach(3K−2,K+5).
```

Lean theorem: `BB6.Agent19.TwoFeeder.reach_two_feeders_iff`.

**Necessity**: every incoming edge into `(4K+4,3)` must be a positive-right odd-left predecessor. A `G(k,1)` branch is arithmetically impossible when `K≡2(mod4)`. The `G` long-right-input branch then has the three source shapes from theorem 1. The odd-left predecessor must itself be preceded by an even-left positive-right hub; evaluating the three shapes yields the two explicit feeder families, while the third forces the even-left even-right ancestor `(14m+6,2m+4)` with `K=4m+2`. Agent 7's power theorem would require `14m+18=14·2^j`, contradicted modulo 7. This excludes the third branch uniformly.

**Sufficiency**: each listed feeder maps in exactly two `T` steps into `(4K+4,3)`, with both finite transitions proved using `G_preimages_mod8_four`. Thus the equation is an exact reachable-set equivalence, not merely a necessary condition.

As a useful specialization, for all `n≥10, n%8=2`, write `b_n=14·2^n−2n−16` and `K_n=(b_n−4)/4`. Then `K_n%4=2`; if the corresponding critical odd-sector hub `(b_n,3)` is blank-reachable, one of the two explicit feeder families must be reachable. Combined with Agent 19's `residual_critical_gateway` and the upstream semantic bridge, this narrows an infinite subset of the actual holdout's remaining halting-event candidates to two fully specified arithmetic families.

The theorem does **not** imply those feeder families are unreachable. Indeed `K=18` has a blank-reachable first feeder `(32,45)`, leading to `(76,3)`; this positive example rules out a naive all-`K` exclusion of either family. Computational examples are explanatory, and not part of the formal theorem.

## Reproducibility and evidence

1. `GDepth.lean` imports Agent 1's `GInverse.lean` and Agent 4's `HaltingFunnel.lean`, proving `G_agree`, `G_critical_inverse_depth_two`, `G_critical_inverse_c_three`, `G_preimages_mod8_four`, and `G_critical_inverse_three_iff`.
2. `TwoFeeder.lean` imports `GDepth` and `ResidualGateway`. Its principal theorem is `reach_two_feeders_iff`, plus `critical_residual_two_feeders`.
3. Manual-only workflow `.github/workflows/agent19-p1-gdepth.yml` checks all real local module prerequisites under pinned Lean 4.36.0-rc2. [Successful GitHub Actions run 41391140177](https://github.com/FlareZ123/bb6/actions/runs/41391140177) (2026-11-02 04:56 UTC).
4. Axiom audits for `reach_two_feeders_iff`, `reachable_two_feeders`, and `critical_residual_two_feeders` all printed `[propext, Classical.choice, Quot.sound]`, with **no `sorryAx`**. The upstream blank-machine bridge was separately certified at pin `ced8f9f44f67a167d5ecc03e687b048c67926371`.

These proofs are an incremental synthesis of Agents 1 and 4's existing lemmas with a stronger source-inverse normal form and its blank-reachable realization. Independent external-prior-art novelty has **not** been established, so all artifacts are retained in `im-results/`.

## Valuable next work

Investigate whether special arithmetic of `K_n=7·2^(n−1)−n/2−5` for `n≡2(mod8)` excludes both remaining reachable feeders simultaneously, or find an actual critical `K_n` entrance. An invariant excluding all `K≡2mod4` is already falsified by the `K=18` example. The central goal remains the **entire remaining infinite critical index family**, especially `n≡2(mod4)`, rather than individual target exclusions.
