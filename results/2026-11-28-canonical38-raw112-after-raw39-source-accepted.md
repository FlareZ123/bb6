# Canonical38: source-accepted Raw112 successor of Canonical39

## Result

The accepted weighted-TNF global quotient now has a source-checked
**38-representative** interface.

Starting from the source-accepted Canonical39 roster obtained after Raw39,
the retained Raw112 parent
`1RB---_1RC---_0RD---_1LD1RE_---1LC_------`
occurs exactly once.  Its independently accepted whole-parent theorem

```text
BB6.Agent47Raw112.parent_cover :
  Cover (WeightedBound 100000) BB6.Agent47Raw112.parent
```

is monotonically lifted to the global floor 6,766,859 and used to remove
that unique representative.  Lean proves

```text
BB6.Agent10Raw112Canonical38AfterRaw39.count38 :
  roster38.length = 38

BB6.Agent10Raw112Canonical38AfterRaw39.raw112_removed :
  (roster38.filter (fun e => sameTable e.2 p112)).length = 0

BB6.Agent10Raw112Canonical38AfterRaw39.sound_integrated :
  ∀ m, compatible root m →
    WeightedBound 6766859 m ∨
      ∃ e ∈ roster38, TNFQuotientCompatible e.2 m
```

and the fixed-score consumer

```text
BB6.Agent10Raw112Canonical38AfterRaw39.exact_at_champion_score
```

shows that Covers for all 38 retained representatives at the proposed
champion score imply `ExactBB6` at that score.

This is a strict improvement of the accepted Canonical39 interface.  It is
**not** a universal upper bound: the 38 retained Cover obligations remain
to be discharged.

## Source acceptance

GitHub Actions run **46150267242** completed successfully on source revision
`ca14c2e30428437b9ff73a1fc810972c3d32f4f4`.

The uploaded evidence artifact is:

- artifact ID **15265958695**
- name `canonical38-raw39-raw112-accepted-delta`
- ZIP SHA-256
  `e0816a258cc41d77be2f225593dcb7768327fde75304e3430ccf0f505ddccd24`

The source checker reconstructed the accepted Raw39 Canonical39 lineage,
authenticated the Raw39 parent transport, authenticated the accepted Raw112
whole-parent artifact, linked the exact Raw112 proof family, and compiled the
final successor from original source.

The recorded root object hashes include:

- `Raw39Canonical40Bridge.olean`:
  `9cb34570102595ebadcc622353f6d3ad42edb11ae9884fdd112050bd6f49cebb`
- `Raw39Canonical39Successor.olean`:
  `73c05636bc570923850fe6ddffb6bbdc6c83a35bea6027d985820fb1ed4903f2`
- `Raw112Canonical38AfterRaw39.olean`:
  `400f1ac80a7b45c74d71c96c9112c8501a2d1666da9c10fa44aa89f76cc57631`

All audited theorems in the cumulative chain depend only on the accepted
standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Provenance chain

The cumulative proof uses:

1. accepted Canonical39 after Raw39: run **46129131784**, artifact
   **15258350500**;
2. accepted complete Raw112 parent: run **46146501930**, artifact
   **15263639929**;
3. the final source-checked Canonical38 consumer: run **46150267242**,
   artifact **15265958695**.

The next exact retained parent with a complete source-accepted whole-parent
Cover is Raw47.  Its removal must be proved on this authenticated roster38
(or on an equivalent authenticated lineage); no arithmetic decrement is
valid by itself.
