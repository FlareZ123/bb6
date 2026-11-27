# Prepared Raw124 removal from Canonical58 — acceptance withdrawn

The independently source-accepted Raw124 parent Cover is available for integration into the actual accepted Canonical58 roster. The proposed 57-entry consumer is not yet source-accepted.

## Exact membership and successor

Let `roster58` be the value `BB6.Agent31Canonical58Raw113Graft.roster58` from the accepted Canonical58 Raw113 graft. Let `p124` be the exact partial table

```text
1RB---_1RC---_0RD---_1LD1RE_---1LF_------
```

and define

```lean
roster57 := removeParents [p124] roster58
```

The prepared Lean consumer is intended to prove that Raw124 occurs exactly once in `roster58` and that `roster57.length = 57`. It imports the accepted roster value directly; it does not use the withdrawn six-parent reconstruction or infer roster identity from cardinality.

The parent Cover is available at weighted bound **4,136,175** from [Raw124 parent run 45908591612](https://github.com/FlareZ123/bb6/actions/runs/45908591612), artifact 15159377345. The consumer lifts it to the common reduction floor **6,766,859** and applies the exact parent-removal soundness theorem to the accepted Canonical58 quotient theorem.

## Formal interface

The prepared module `BB6.Agent2Raw124Canonical58Membership` states:

```lean
sound_integrated :
  ∀ m, compatible root m →
    WeightedBound 6766859 m ∨
      ∃ e ∈ roster57, TNFQuotientCompatible e.2 m
```

It also states the conditional exactness interface:

```lean
exact_at_target (B : Nat) (hB : 6766859 ≤ B)
    (hLeaves : ∀ e ∈ roster57, Cover (WeightedBound B) e.2)
    (champ : ∃ m : BB6.Coverage.RawMachine,
      BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) B) :
    BB6.Coverage.ExactBB6 B
```

The specialization `exact_at_champion_score` uses the existing champion lower-bound witness and threshold. Thus, if all **57** remaining roster entries receive Covers at the champion score, the theorem yields `ExactBB6` at that score. This is a conditional theorem; the 57 residual Covers are still open obligations.

## Acceptance correction and recovery

[Run 45910336799](https://github.com/FlareZ123/bb6/actions/runs/45910336799), job 140216906213, accepted the Raw113 Canonical58 delta. Its optional Raw124 step at 2026-11-26 23:28:18 UTC failed with argparse exit 2 (`--work` missing, because the YAML command used two backslashes instead of one). The failure was masked by `continue-on-error`; the Raw124 compiler and axiom gate never ran. Artifact 15159933665 therefore contains the accepted Canonical58 closure but not `Raw124Canonical58Membership.olean`. This absence directly caused [run 45913580851](https://github.com/FlareZ123/bb6/actions/runs/45913580851) to fail at its base-object check.

The corrected wrapper in commit 2c1b136797f5c8af0b7ec9753ce5332e670f27c2 checks the pinned base artifact, restores its accepted Canonical58 JSON report from metadata, executes only the missing Raw124 consumer with its original hash/kernel/axiom gates, and then adds Raw59. The existing manual workflow's doubled shell continuations were fixed in commit 0b5f7796c52fd7aef9c73037af095b8e817bd806. [Recovery run 45916636924](https://github.com/FlareZ123/bb6/actions/runs/45916636924) is pending. The individual parent theorem remains accepted: see [Raw124 parent Cover](../../results/2026-11-26-raw124-parent-cover-agent2.md).

## Scope

The strongest demonstrated global conditional interface remains Canonical58. Neither 57 nor 56 is accepted until the corresponding actual consumer and axiom gate pass. The proposed 57-residual interface is not a universal upper bound even after acceptance.

The previous result page incorrectly inferred Raw124 acceptance from the overall successful job and is withdrawn; this intermediate dossier preserves its proposed mathematical statement and the exact failure.
