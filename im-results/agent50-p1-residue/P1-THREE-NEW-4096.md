# Three additional all-time P1 critical-gate exclusion classes

**Agent 50, 2026-11-02. Scope: intermediate source-certified mathematical research; BB(6) and P1 remain undecided.**

For the authentic blank-entry `BB6.Agent1.Reach` accelerated dynamics of holdout `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`, each of the following infinite families is rigorously excluded:

```lean
∀ q : Nat, ¬BB6.Agent1.Reach 2 (14*2^(4096*q+226)-2*(4096*q+226)-10)
∀ q : Nat, ¬BB6.Agent1.Reach 2 (14*2^(4096*q+482)-2*(4096*q+482)-10)
∀ q : Nat, ¬BB6.Agent1.Reach 2 (14*2^(4096*q+914)-2*(4096*q+914)-10)
```

The first two indices lie in the previously unresolved n≡34(mod64) family; the third lies in previously unresolved n≡18(mod64).

| Class n mod4096 | Source SHA-256 (compressed tar.xz) | Actual unmodified-source Lean CI |
| --- | --- | --- |
| 226 | `24cf176a58c5f65b18f571cd1363334448801431b37b9df3e1ac36a208534eed` | [41402955675, success](https://github.com/FlareZ123/bb6/actions/runs/41402955675) |
| 482 | `b0e7be8f65944338e425d698a65298fdb15f1c3a9ae5239358459e96d5bf9c05` | [41404017432, success](https://github.com/FlareZ123/bb6/actions/runs/41404017432) |
| 914 | `53c070a4f78484c800ef1aa72fdd99b7afdad8fc4bea22461f18dc73ecd1985d` | [41404766229, success](https://github.com/FlareZ123/bb6/actions/runs/41404766229) |

Each is a self-contained chain of 11 Lean modules `Inverses.lean`, `CertReach1..8.lean`, `PowerBand.lean`, `SourceBridge.lean`, in the respective [226](./P1Cert226.tar.xz.b64), [482](./P1Cert482.tar.xz.b64), and [914](./P1Cert914.tar.xz.b64) source archives. Three manual workflows [226](../../.github/workflows/agent50-p1-226-verify.yml), [482](../../.github/workflows/agent50-p1-482-verify.yml), [914](../../.github/workflows/agent50-p1-914-verify.yml) check archive SHA, compile the original unmodified upstream Agent1 and Agent50 prerequisites, then all new sources under pinned Lean 4.36.0-rc2. Final three theorem axiom audits are exactly `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

## Proof architecture

For each base `B∈{226,482,914}`, set `n=4096q+B`, `t=7·2^(4096q+B−12)−q`. `critical_target_implies_three` forces the positive odd-sector G return `(8192t−2B−16,3)`. Exact inverse classifications through the real `GAncestor` constructors yield 23 reachable odd-sector hubs, feeding 46 terminal contradictions from the already-certified blank-reach invariants: every even-left positive-right hub has first counter 2 or 0(mod4), and every reachable positive-even-right even-left hub must satisfy `a+12=14·2^j`. Explicit bounds on all 23 prospective power leaves place them inside a single interval where no `14·2^j` exists.

The 226 class uses power leaves in `4256t−460 ≤ z ≤ 8032t`; the 482 class uses `4256t−962 ≤ z ≤ 8032t`; the 914 class uses `4376t−1800 ≤ z ≤ 8000t`. The general uniform bound `4200t−2000 ≤ z ≤ 8100t` works for the second and third. For all q, `t≥10000(q+1)` implies `14·2^(n−1) < z < 14·2^n`, a contradiction to the power shape. No finite sampling horizon enters any theorem.

The [226 proof dossier](./P1-226-MOD4096.md) explains the first proof in more detail.

## General-purpose certificate generation

The separate [symbolic generator archive](./P1CertGenerator.tar.xz.b64) contains Python `symbolic.py`, `generate.py`, `build_case.py`, plus verified Lean arithmetic/source-bridge templates. SHA-256 of compressed tar.xz: `583841e00381d6ec955a7bd38d32c5a66c4c3e1e623e8030ed343414fa27e61a`. It generates a full 23-hub Lean proof package for selected 4096-residue classes, with a conservative common power envelope. The generator is a **search and proof-authoring tool**, not a proof oracle; a generated class is established only after the resulting Lean code compiles against actual source modules with a standard-axiom audit. A manual [13-class CI matrix](../../.github/workflows/agent50-p1-matrix-13-verify.yml) tests candidates in parallel; its results must be inspected individually before making any claims.

**Remaining uncertainty:** An infinite number of other critical indices are still unclassified, and no complete original-machine nonhalting theorem, BB(6) upper bound, or exact BB(6) value follows from these exclusions.
