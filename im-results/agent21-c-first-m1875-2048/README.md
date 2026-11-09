# Machine C low-stopping family: an infinite 2048-residue exclusion

**Original-source Lean 4.36.0-rc2 certified, 9 November 2026.** The complete original-source proof passed [manual CI run 42584937734](https://github.com/FlareZ123/bb6/actions/runs/42584937734) (job 129052391270), importing the unchanged Machine C section map and the independently verified exact inverse grammar. The final theorem's axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound`. This is a genuine all-time blank-orbit exclusion. Machine C and BB(6) remain unsolved.

## Exact theorem

Let `F = BB6.Agent46.secNext` denote the original two-counter Machine C section map with the authentic blank entry `(5,1)`. Our source theorem is

```lean
BB6.Agent21Low1875.blank_no_1875_low (time t : Nat) :
  BB6.Agent8Section.run F time (some (5,1)) ≠ some (1, 2048*t+515)
```

Consequently, the source-certified low stopping equation `k+3*m+4=2^(2*m+3)` is inaccessible whenever `m % 2048 = 1875`. This is theorem `first_stop_m1875_mod2048`, quantified over **all** natural `time,m,k`. In the previously discussed neighboring family `m≡339(mod512)`, this removes its `1875(mod2048)` quarter; it does not exclude the other three residues.

## Exact backward proof

Write `t≥0`, the stopping point `T=(1,2048t+515)` and its unique possible section parent `P=(1024t+256,1536t+384)`. The complete original inverse grammar proves the following exhaustive parents of `P`:

| Parent | First coordinate | Second coordinate | Obstruction |
| --- | ---: | ---: | --- |
| A | `40t+8` | `2028t+497` | Odd right counter, coordinate sum 1 mod 4 |
| B | `160t+38` | `1968t+485` | Its unique predecessor is `(1064t+259,1516t+371)`, with odd right counter and sum 2 mod 4 |
| C | `640t+158` | `1728t+428` | Its unique predecessor is `(2368t+584,864t+213)`, with odd right counter and sum 1 mod 4 |
| D | `2560t+638` | `768t+191` | Odd right counter, coordinate sum 1 mod 4 |

Every successful section output with odd second coordinate at least five has coordinate sum congruent to **0 or 3 mod 4**. Thus A, D, and the forced predecessors of B and C cannot be in the image of any real section edge. None is the initial `(5,1)` state. This excludes P at every blank-origin time and hence T, with no finite search depth or parameter cutoff.

The arithmetic proof actually constructs `Local1875.Reach`, an unbounded inductive ancestry relation that allows arbitrary low-right-output transitions. Its high-output predicate is a literal copy of the original complete high-output inverse predicate, and `Low1875Source.lean` proves definitional agreement with the unchanged source. All exceptional lower-output source transitions remain allowed in the induction; they do not weaken the forbidden high target proof.

## Source and reproducibility

- [`Low1875Arithmetic.lean.xz.b64`](Low1875Arithmetic.lean.xz.b64) is the full local Lean kernel proof, SHA-256 of decoded source `0da0704569dd55cc60b8c1dec8fd75b79220d19574f27c5901c76dcd13f44625`.
- [`Low1875Source.lean`](Low1875Source.lean) is the readable original-source bridge, exact finite-run equivalence, and all-time halting-parameter corollary.
- [`agent21-low1875-source.yml`](../../.github/workflows/agent21-low1875-source.yml) is the reusable **manual-only** source check; it reconstructs the SHA-verified arithmetic proof and compiles the unchanged dependencies before the final bridge.
- The successful CI log shows standard Lean axioms for `runF_no_low`, `blank_no_1875_low`, and `first_stop_m1875_mod2048`, with no `sorryAx`.

## Scope and strongest comparison

This theorem sits below `im-results/` because a globally new Machine C decision or independent external novelty has not been established. [Agent 38's source-certified `m≡83(mod512)` theorem](../agent38-low259/README.md) treats the adjacent stopping coordinate `k≡259(mod512)`; its dossier identified the `k≡3(mod512)` branch as harder. The current proof handles a precise infinite subfamily of that branch. [Agent 45's complete three-ancestor image theorem](../agent45-c-three-step/README.md) may imply this missing-ancestor sector by a more general **paper/finite-table** classification, which has not itself been Lean source-certified; review whether our specialized source theorem is subsumed. Do not independently claim external priority.

Remaining target: exclude the other `m≡339(mod512)` residues, or construct a stronger unbounded true-blank invariant that resolves the entire stopping existential.
