# Source-certified pumped E/0 halting cylinders for D (Agent 31, 2026-11-04)

**Classification:** mathematically certified *intermediate synthetic-input result*. The original blank-tape six-state D holdout is **not decided**; no new global BB(6) bound or publishable holdout decision is asserted.

Machine: `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---` (Cryptid D), with F/0 returning across the physically blank left tape. In the source `CryptidBoundary` model, let `I_a(w)` denote state F reading 0, blank tape to the left, and right tape `1^a w` followed by implicit infinite zeros.

## Rigorous theorem

For **all** naturals `k,n` and **every** finite Boolean suffix `Y`, from

```
I_(3k+4) (0 110110 (10)^n 0 Y)
```

the first halt occurs after exactly

```
T(k,n) = 12*k*k + 41*k + 99 + 4*n
```

primitive transitions. The final zero *before* `Y` is essential to this specific universal cylinder; arbitrary input after it is allowed.

Original-source Lean statements in `BB6.Agent31PumpHalt`:

- `e66_pairs`: **arbitrary** untouched left remainder `L` and right suffix `Y` at E/0, with `00 1 L` immediately left and `110110 (10)^n 0 Y` right, reaches the halting state in `66+4*n` transitions.
- `e65_pairs`: exactly one transition earlier the state is F, allowing an all-earlier-time nonhalting proof via the original machine's frozen-halting semantics.
- `full_E_011011_pairs_halt`: composes `e66_pairs` with the original universal `CryptidBoundary.prefix_E` (the `12*k*k+41*k+33` step E-entry lemma).
- `full_E_011011_pairs_first`: every time `t < T(k,n)` is nonhalting, for all `Y` without a search-depth bound.

The exact proof uses a 19-step E-to-B finite boundary, then an all-parameter B-forward `(10)^n` sweep of `2*n` steps, a B/0 step, an all-parameter C-backward `(01)^n` sweep of `2*n` steps, and a final finite 46-step C-to-halt segment. This gives the observed **four extra raw transitions per additional 10 pair**, with a proof for unbounded `n`.

## Reproduction and original-source connection

- The [Lean proof archive](EPairHalt.lean.xz.b64), decoded by [checksum-pinned atomic restorer](restore_pair_halt.py), has uncompressed SHA256 `f88d195ca970879989428c5f9beda41700d045e36cea6b4df8b6005c25a79c1c` (8,416 bytes).
- Original `Boundary.lean` comes from [Agent 31's pinned source archive](../agent31-cryptid-boundary/Boundary.lean.xz.b64); run the already-existing `agent31-d-exceptional-source.yml` manual workflow.
- [Original-source Lean CI #41773165827](https://github.com/FlareZ123/bb6/actions/runs/41773165827) passed on 2026-11-04. Axiom audits for the final halting and first-halt theorems returned **`[propext, Quot.sound]`**, without a custom `prefix_E` axiom, `sorryAx`, or `native_decide`.
- Independently, a direct sparse-tape raw interpreter tested **5,000** combinations (`0<=k<40`, `0<=n<25`, five seeded random `Y` per pair, length up to 20). All first-halt times matched `T(k,n)`. This is merely secondary finite evidence.

## Relevance, limitations and prior art

This establishes a new explicit forbidden right-tape cylinder to exclude (or prove reachable) in an eventual blank-root closure proof. Its `110110` E-right prefix is distinct from Agent 2's previously certified `1011011000` halting cylinder. The theorem follows from the original `prefix_E` formula, not a reimplementation of the table. It is a two-parameter family of *synthetic F/0 inputs* and is not a new result about the actual blank orbit until a reachability theorem is proved.

The immediate unsolved obligation is whether any source-certified blank-root D return (including exceptional descendants and the different D3/D1/D2 roots) enters `I_(3k+4)(0 110110 (10)^n 0 Y)`. Existing regular packet languages do not already imply this. A positive genuine-root witness would decide the machine's halting; an invariant excluding all reachable forms would strengthen nonhalting evidence but does not follow from this theorem.
