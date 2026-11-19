# Four-slot translated nonhalting cylinder

## Exact transition table

The candidate fixes only four of the twelve transition inputs:

| Input | Action |
|---|---|
| A/0 | 1RB |
| B/0 | 1LC |
| C/1 | 0RD |
| D/1 | 1RB |

All eight other rows are arbitrary. In conventional two-symbol, six-state notation, the cylinder therefore contains exactly

`25^8 = 152,587,890,625`

machines.

## Blank-root translated cycle

Starting with a blank tape:

| Successful moves | State | Head | Marked cells |
|---:|---|---:|---|
| 0 | A | 0 | `{}` |
| 1: A/0 | B | 1 | `{0}` |
| 2: B/0 | C | 0 | `{0,1}` |
| 3: C/1 | D | 1 | `{1}` |
| 4: D/1 | B | 2 | `{1}` |
| 5: B/0 | C | 1 | `{1,2}` |

The two-step entry reaches C/head 0 with finite support `{0,1}`. The three-step macro C/1, D/1, B/0 returns to C/head 1 with finite support `{1,2}`. The state is unchanged, the head has shifted by +1, and every marked cell has shifted by +1. The next three steps therefore repeat the same translated macro. This argument uses no transition outside the four fixed rows, so it applies to every total completion of the partial table.

## Lean proof artifacts

- `TranslatedFourSlot.lean` defines the exact four-slot partial machine and asks the existing `finiteTranslatedCheck` checker to verify entry length 2 and period 3.
- `agent27Four_cover` lifts that finite witness through the already established `finiteTranslatedCheck_sound` theorem to every completion.
- `agent27Four_never` specializes the cover at bound 0 and derives `NeverHalts`.
- `agent27Four_mass` and `agent27Four_mass_numeric` state the exact cylinder mass.

The underlying translated-cycle soundness theorem is in Agent 24's `TranslatedFiniteOracle.lean`; it proves that a positive-length finite-support translation forces an infinite run on the original two-way infinite tape.

## Candidate global-frontier integration

`FourSlotLeafGraft.lean` is a proposed exact graft into `depth4ResidualAudit`. It checks the existing oracle at the four prefixes, verifies the physical first-unknown sequence A/0, B/0, C/1, D/1, and uses `addCertificate_open_iff` to show that the four-slot cylinder is removed from the old open frontier without discarding any incompatible open completion.

An independent V8 port of the current finite-support and oracle definitions evaluated:
- `finiteTranslatedCheck p 2 3 = true`;
- `lassoDecisionOracle p 6 6 12 2 4 = false`;
- `firstUnknownPhysical p 12 finiteBlank = none` after all four rows are fixed;
- each prefix's first unknown is respectively A/0, B/0, C/1, D/1;
- the finite-halt, finite-ray, zero-mask, exact-lasso, and finite-entry-macro subchecks all reject the four-slot table at the current depth-four parameters.

This is a reproducible source-level computation and a direct transition derivation, not a Lean compile result. The exact new source module and full graft wrapper have **not yet passed local Lean preflight**. The wrapper's `by decide` checks and exported axiom profiles must be compiled before describing the integrated frontier result as accepted or updating the interpreted frontier report. Do not substitute CI for the local gate unless the research coordinator explicitly changes that rule.

## Relation to the five-slot sibling

The earlier five-slot cylinder fixes D/1 = 1RE and E/0 = 1LC. This four-slot cylinder fixes D/1 = 1RB instead, so the two cylinders are disjoint. The four-slot candidate is 25 times larger and closes the same general class of translated finite-support behavior with one fewer fixed input.

This is a nonhalting family, not a decision of the remaining BB(6) machines and not a universal runtime upper bound.
