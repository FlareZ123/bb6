# CTL certificate partialization for Raw10

Status: **promising, not yet Lean-verified**. The generic congruence argument is straightforward, but the current CI run is still compiling the formal adapter.

## Core observation

The pinned upstream file `BusyBeaver/Calculi/CtlCertificate.lean` defines `ctlCheck M dL dR acc` and proves `ctl_certificate_implies_is_does_not_halt`. The machine argument is read only by `closureOk` on tuples `(p,s,a,q)` in `acc), specifically through `M s a`. Thus, if two machines agree on every state-symbol pair projected from `acc), their `ctlCheck` values are equal. A generic `ctlCheck_congr` lemma should therefore transfer the upstream nonhalting proof to every completion of the partial table that fixes just those pairs.

This is stronger than forgetting a single halt row: all unused ordinary transitions can also be left unconstrained.

## Two pinned Raw10 source certificates

Both upstream modules have A0 = 1RB and B0 = 1LC, so they refine the Raw10 parent.

### Four-pair certificate

Source module:
`BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH`

Its `ctlAcc` projects to only four state-symbol pairs:

| Slot | Transition |
|---|---|
| A0 | 1RB |
| B0 | 1LC |
| C1 | 1LE |
| E0 | 0LE |

The resulting partial table has 4 assigned transitions and 8 holes, hence exactly
`25^8 = 152,587,890,625` completions. The source machine's F1 halt transition is not fixed by this partial table.

### Five-pair certificate

Source module:
`BusyBeaver.BB6.NonHalt.M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA`

Its `ctlAcc` projects to five pairs:

| Slot | Transition |
|---|---|
| A0 | 1RB |
| A1 | 0RC |
| B0 | 1LC |
| C0 | 1RA |
| C1 | 1RC |

This leaves 7 holes, hence `25^7 = 6,103,515,625` completions. The two partial tables are disjoint because their C1 transitions differ (1LE versus 1RC).

## Crosswalk against the current exact Raw10 complement

The current complement has 41 disjoint boxes after the 65 side witnesses, held block, box-8 cycle, and box-0 halt certificates.

A product-domain intersection calculation gives:

- The four-pair cylinder is fully contained in the 41-box complement; it intersects six boxes, and the six intersection masses sum to exactly `25^8`.
- The five-pair cylinder is fully contained in the complement and lies wholly in one box.
- The two cylinders are disjoint.

Subtracting the four-pair cylinder alone gives 47 boxes and residual mass
`90,584,915,823,100`, removing `152,587,890,625` completions.

Subtracting both cylinders in the order five-pair then four-pair gives 51 boxes and residual mass
`90,578,812,307,475`, removing `158,691,406,250` completions.

These crosswalk numbers are computed from the exact product domains, not inferred from the 100,000-step simulations. They still need to be reproduced by the Lean remainder definitions before being treated as formal results.

## Formalization in progress

- `Raw10CtlPartialLeaf.lean` defines the local-to-Cryptids inverse adapter, `ctlCheck_congr`, the four-pair partial table, an all-completions nonhalting theorem, a `WeightedTNFCertificate`, and the 47-box exact remainder/cover consumer.
- CI run `45709376748` is compiling this file together with the previous one-hole pilot.
- The prior run failed before compiling the source leaf because `Raw10Box0Halt` and `Raw10Box8Cycle` opened obsolete namespaces. Those opens were corrected to the current `BB6Coverage` and `BB6.Agent13BlankDelay` namespaces, and `Mathlib.Tactic` was imported for `interval_cases`.
- The current formal file covers the four-pair cylinder only. The five-pair cylinder should be added after the generic adapter and congruence lemma compile.

## Next steps

1. Complete CI compilation of `Raw10CtlPartialLeaf.lean`; resolve Lean errors at the smallest relevant point.
2. Confirm the kernel axiom profile for `ctlLeaf2_neverHalts`, `ctlLeaf2Certificate`, and the exact 47-box remainder.
3. Factor the completion theorem into a generic CTL-partialization lemma and add the five-pair certificate.
4. Recompute the combined 51-box remainder and prove the exact mass reduction in Lean.
5. Keep this in `im-results/` until the source adapter, all-completions theorem, and exact remainder are independently reproduced.
