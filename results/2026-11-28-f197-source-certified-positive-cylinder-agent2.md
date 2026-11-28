# F197: original blank-start nonhalting for every completion of an eleven-row six-state table

**28 November 2026.** This is an original-source Lean 4.36.0-rc2 theorem for a nontrivial infinite family of configurations of the six-state, two-symbol F197 machine
`1RB0RE_1RC0LE_0RD---_0RE0RA_1LF0LB_1LA1LF`.
The original blank-start theorem is now **source-accepted**: `F197.Agent2Self.blank_nonhalt` proves every finite primitive transition of the actual blank run exists, and `F197.CoverBridge.blank_cover` lifts this to **all 25 legal completions of the sole unspecified C1 transition**, with a `Cover (WeightedBound B)` for every finite bound `B`. The exact self-embedding on an infinite tape cylinder is the essential infinite-time certificate. This closes the F197 root/partial-leaf obligation, but **not** its Raw132 parent (which also contains the distinct F321 holdout) and **not** BB(6).

## Exact mathematical assertion

Use the literal Turing-machine semantics in [Macro.lean](../im-results/agent31-f197-macro/Macro.lean), where `B(a,e)` has state B, inclusive left tape `a`, and right tape `00e`; `e` is a one followed by zeros. Let the finite aligned words be

```
A = 10, T = 1100, J = 100, U = 11100
P = AAT
L = AATAAATAUJTT
HEAD = JTAATAAATATAATAATAATAATTATAATAATAATTAATTAAATAUJTT
```

The Lean theorem `F197.Agent2Self.self_embedding` asserts that **for every infinite left suffix** `l` whose leading bit is 1 there exists a strictly positive finite primitive-machine execution

```
B(P^72 HEAD L^35 l, e)  -->+  B(P^72 HEAD L^35 f(l), e).
```

Here `f` is an explicit guarded suffix transformer: in the checked proof it prepends seven `L` blocks, then `732592001087343536` additional `L` blocks, then `T` and a fixed finite marker continuation `Y`, before the unchanged `l`. Equivalently the `L` exponent in the prefix of `f(l)` is **732592001087343543**. Every such new suffix still starts with a 1. In particular, iterating this positive return yields a well-defined infinite execution of the literal F197 transition table for **every** configuration in this cylinder. Since `L=AATAAATAUJTT` has precisely **36 physical tape bits**, this source-certified return explicitly inserts **26,373,312,039,144,367,548 bits** just from its repeated `L` prefix, apart from the further `T` and finite marker word. This counts actual encoded tape bits, not macro steps; repetition yields an arbitrarily long growing prefix while the retained suffix is never inspected.

The stronger `F197.Agent2Self.self_nonhalt` proves directly:

```lean
∀ (l : Tape), l 0 = true →
  ∀ t : Nat, run t (state 72 START l) ≠ none
```

where `START = HEAD ++ flat L 35` and `state` prepends the indicated `P` power with the exact right-blank boundary. This all-time conclusion is **not** inferred merely from a long finite run: it follows by indefinitely composing the proved positive, suffix-parametric return.

## Authentic blank start, exact source proof and weighted Cover

The generated Lean theorem `F197.Agent2Self.blank_to_cylinder` states that for the **literal six-state blank configuration** there exist a 1-leading suffix `l` and a finite positive source-run length `k` such that

```lean
Reach blankStart (state 72 START l)
```

where `START = HEAD ++ flat L 35`. The proof first checks the exact 5,810,803-step primitive seed, then composes 181 source-faithful accelerated epochs through 10,477 guarded trace entries, and finally exposes the recurrent cylinder. It uses the already-certified unbounded suffix-parametric self-return; there is no appeal to observed finite longevity as a substitute for a liveness proof.

The exported theorem `F197.Agent2Self.blank_nonhalt` proves

```lean
∀ t : Nat, F197.run t F197.Agent2Self.blankStart ≠ none
```

and the exact **original integer-tape machine** bridge exports

```lean
F197.CoverBridge.blank_cover (B : Nat) :
  BB6Coverage.Cover (BB6.Agent13BlankDelay.WeightedBound B)
    F197.CoverBridge.table
```

The partial table has 11 defined rows; `C1` is the only hole, with 25 choices (including halting). The Cover statement universally quantifies *each* compatible completion, proves it never halts from the authentic blank tape, and therefore supplies the weighted score bound at **every** `B`. [F197BlankCover.lean](../im-results/agent2-f197-sweep/F197BlankCover.lean) composes the original-machine transport and the source blank theorem without an unproved leaf hypothesis. The `table_eq_rows` and `only_hole` declarations certify the exact fixed table and sole hole.

The complete original-source Lean 4.36.0-rc2 build succeeded twice: [monolithic root run 46094787881](https://github.com/FlareZ123/bb6/actions/runs/46094787881) (source `b8729d41a34617aece0eb1e9cc7c7211988a3d96`) and [four-shard full composition run 46100750502](https://github.com/FlareZ123/bb6/actions/runs/46100750502) (source `e1c4fbf9e48b46154e3c2cbf3d13aa1db628dfac`). The latter successfully compiled all generated RootParts and then `RootTheorem.lean`, `Frontier`, `BlankDelayKernel`, `SparseBlankDelay`, `CoverBridge`, `F197WeightedLeaf`, and `F197BlankCover`, emitted theorem axiom reports, and rejected any `sorryAx` in the collected final log. This is a proof of one named partial-table family, not an exhaustive global upper bound.

## Robustness under all physical completions

The source-certified cylinder liveness has been transported to the **original six-state machine semantics** of [CoverBridge.lean](../im-results/agent31-f197-macro/CoverBridge.lean). The Lean theorem [`F197.CoverBridge.original_cylinder_live`](../im-results/agent2-f197-sweep/F197CylinderCover.lean) states, without assuming that the C1 instruction is a halt:

```lean
∀ (m : BB6Coverage.Machine), compatible table m →
  ∀ (c : BB6Coverage.Config) (l : F197.Tape), l 0 = true →
  Related c (F197.Agent2Self.state 72 F197.Agent2Self.START l) →
  ∀ t : Nat, BB6Coverage.run m t c ≠ none
```

Thus **every one of the 25 completed physical transition tables** extending the literal 11-entry F197 partial machine stays live forever once in the indicated state/tape cylinder. In particular, the result is insensitive to whether C1 is a halting transition or any of the 24 nonhalting write/direction/target choices. This cylinder theorem is independently stronger in its initial-configuration scope than the single blank-root theorem; the new source-accepted blank-root composition above also proves the authentic blank-start verdict for all these completions. The exact original-source Lean 4.36.0-rc2 compilation [run 46100999285](https://github.com/FlareZ123/bb6/actions/runs/46100999285) accepted `original_cylinder_live` with axioms only `propext`, `Classical.choice`, and `Quot.sound`, no `sorryAx`. The proof uses the source-faithful `run_related` bisimulation for every compatible complete machine.

## Proof architecture and accepted evidence

- Each finite local step is reduced to the original six-state literal transition rules, with explicit known-prefix/read guards. `Macro.lean` and [PrefixCheck.lean](../im-results/agent2-f197-sweep/PrefixCheck.lean) prove source-faithful interpretation for arbitrary untouched suffixes.
- Symbolic descent, terminal decoding, marker transfer, and reset cycles are established in the [EpochMarker/CounterCore/OrdinaryBulk family](../im-results/agent2-f197-sweep/README.md). The decisive trace has 3,765 local/ordinary transitions before a parity-controlled marker epoch and 256 after it. The marker multiplies the retained `L` reservoir without enumerating its 732-trillion-sized exponent.
- The [generators](../im-results/agent2-f197-sweep/generate_lean_trace.py) produce 658 distinct packed finite-operation checks and chunked source-specific Lean proof terms. Every operation bank is connected through the soundness theorem of [PackedCheck.lean](../im-results/agent2-f197-sweep/PackedCheck.lean); the final `SelfTheorem.lean` is generated reproducibly from the [exact checker](../im-results/agent2-f197-sweep/verify_nonhalt.py).
- **Original-source Lean acceptance:** [GitHub Actions run 46094555223](https://github.com/FlareZ123/bb6/actions/runs/46094555223), source commit `45965d2deb2360930b25be1e134d1ce741be34a9`. The entire `self_embedding`/`self_nonhalt` dependency closure compiled using pinned Lean 4.36.0-rc2 and printed only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`. The separately run [exact independent Python certificate check](https://github.com/FlareZ123/bb6/actions/runs/46094784084) also passed.

The original stand-alone computational proof used a **narrower** cylinder with `L^80`; the source-certified theorem strengthens its starting family to `L^35`. The reconstructed source code and integer parameters are sufficient to replay the proof; no finite-only liveness assertion is silently promoted to an infinite claim.

## Scope toward BB(6)

**Closed:** the F197 literal blank run and every total six-state extension of its eleven-row partial table are source-certified nonhalting at all time bounds. The exact partial-table weighted Cover is available for integration into the current Raw132 descendant classifier. **Open:** the remaining Raw132 complement, including the distinct F321 root, the complete Raw132 parent Cover, and all other retained Canonical40 Covers. No exact BB(6) upper bound is asserted. The [current Canonical40 interface](2026-11-27-canonical40-raw57-reduction-agent29.md) retains 40 globally unproved parent hypotheses; this leaf-level theorem does not decrease that count by itself.
