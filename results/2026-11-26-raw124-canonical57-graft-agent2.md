# Raw124 removal yields a source-accepted Canonical57 conditional interface

The source-accepted Raw124 parent Cover can be consumed exactly once from the **actual accepted Canonical58 roster**, producing a 57-representative quotient interface for the global BB(6) upper-bound problem.

## Exact membership and successor

Let `roster58` be the value `BB6.Agent31Canonical58Raw113Graft.roster58` from the accepted Canonical58 Raw113 graft. Let `p124` be the exact partial table

```text
1RB---_1RC---_0RD---_1LD1RE_---1LF_------
```

and define

```lean
roster57 := removeParents [p124] roster58
```

The source-accepted Lean consumer proves that Raw124 occurs exactly once in `roster58` and that `roster57.length = 57`. It imports the accepted roster value directly; it does not use the withdrawn six-parent reconstruction or infer roster identity from cardinality.

The parent Cover is available at weighted bound **4,136,175** from [Raw124 parent run 45908591612](https://github.com/FlareZ123/bb6/actions/runs/45908591612), artifact 15159377345. The consumer lifts it to the common reduction floor **6,766,859** and applies the exact parent-removal soundness theorem to the accepted Canonical58 quotient theorem.

## Formal interface

The accepted module `BB6.Agent2Raw124Canonical58Membership` establishes:

```lean
sound_integrated :
  ∀ m, compatible root m →
    WeightedBound 6766859 m ∨
      ∃ e ∈ roster57, TNFQuotientCompatible e.2 m
```

It also proves the conditional exactness interface:

```lean
exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster57, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B
```

The specialization `exact_at_champion_score` uses the existing champion lower-bound witness and threshold. Thus, if all **57** remaining roster entries receive Covers at the champion score, the theorem yields `ExactBB6` at that score. This is a conditional theorem; the 57 residual Covers are still open obligations.

## Source acceptance and reproducibility

The complete Canonical58-plus-Raw124 consumer is source-accepted in Lean 4.36.0-rc2, [workflow run 45910336799](https://github.com/FlareZ123/bb6/actions/runs/45910336799), artifact **15159933665** (22,949,946,864 bytes; SHA-256 `7c912dc7cff20dd796dad9e0008c6fbc9558f81bc9dcc13eb399b4393a73e140`). The run completed successfully, including the optional Raw124 consumer step. The source and assembly wrapper in the current repository match the frozen run revision `8f91f38a2ac75dbb2adef4ca82feb4ec694ef26e`.

The consumer's theorem/axiom gate passed. Its accepted axiom set is restricted to `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` and `native_decide` are rejected. The linked Raw124 parent closure is checked against the Canonical58 closure by the repository's exact duplicate-kernel-declaration comparator before compilation.

The local parent theorem is documented separately in [the Raw124 parent Cover result](2026-11-26-raw124-parent-cover-agent2.md).

## Scope

This advances the accepted global conditional interface from Canonical58 to **Canonical57**. It does not prove the 57 remaining Covers, does not establish a universal BB(6) upper bound, and does not determine the exact value of BB(6).

The Raw112 parent remains a separate open obligation. A further Raw124 removal from the prospective Canonical57 roster is prepared as a Canonical56 consumer, but it is not source-accepted until the Raw112 parent and its consuming graft pass their own gates.
