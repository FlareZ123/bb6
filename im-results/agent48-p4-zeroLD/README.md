# P4 exact child grafts: finite lasso, translated-cycle, and fresh-ray certificates

**Status:** 28 new disjoint source-cylinder certificates are drafted for the P4 depth-four parent. The Lean modules and exact report theorems are **not yet accepted**. Local preflight is unavailable in this invocation. The first three targeted CI runs did not accept a P4 module: runs 45354239582 and 45354469278 stopped in unrelated optional WordLasso code; run 45354692563 reached the P4 step and exposed invalid namespace-qualified module imports. Those imports are corrected here, and the source draft now includes five additional simple D/0 cylinders. A new targeted run is required. Keep this work in `im-results/`.

## Authenticated parent and blank entry

P4 fixes the original TM63 rules:

| Slot | Rule |
|---|---|
| A/0 | 1RB |
| B/0 | 1LC |
| C/1 | 0RD |
| D/1 | 1RE |

After four successful moves from blank tape, the machine is in E at head 2, with cell 1 marked and the entire right ray from the head blank. The existing Agent27 graft already certifies E/0 = 1LC by a translated finite-support cycle.

## First-level E/0 children

The seven new E/0 certificates are:

| E/0 action | Certificate | Length | Shift |
|---|---|---:|---:|
| 0LD | exact configuration repeat (steps 4 and 6) | 2 | 0 |
| 0RE | fresh right ray | 1 | +1 |
| 1RE | fresh right ray | 1 | +1 |
| 1RB | fresh right ray | 4 | +2 |
| 0RA | fresh right ray | 5 | +3 |
| 1RA | fresh right ray | 5 | +3 |
| halt | immediate halt after the four-move prefix | — | — |

Together with the already certified 1LC child, these account for eight of the 25 E/0 actions. The other 17 E/0 children remain open.

Each first-level child fixes five slots and has mass (25^7=6,103,515,625). The seven new children are pairwise disjoint because they assign different actions to E/0.

## Deeper E/0 branches

Two additional E/0 branches admit D/0 refinements.

### E/0 = 0LC

The six-move blank entry A/0, B/0, C/1, D/1, E/0, C/1 clears the tape and reaches D at head 2 on a blank tape. Ten D/0 children have source certificates:

| D/0 action | Certificate | Length | Shift |
|---|---|---:|---:|
| 0LD | translated finite support | 1 | -1 |
| 0LA | translated finite support | 7 | +1 |
| 0RA | fresh right ray | 7 | +3 |
| 1RA | fresh right ray | 7 | +3 |
| 1RB | fresh right ray | 6 | +2 |
| 0RD | fresh right ray | 1 | +1 |
| 1RD | fresh right ray | 1 | +1 |
| 1RE | fresh right ray | 3 | +1 |
| 1LD | fresh left ray | 1 | -1 |
| halt | immediate halt at the six-move entry | 0 | — |

The translated checks compare the entire finite marked-cell support. The 1LD child is a leftward fresh-ray proof: D/0 writes 1, moves left, and re-enters D on the next blank cell; the six-step entry has a pristine left ray. The halt child stops immediately at the D/0 slot.

### E/0 = 0RD

The five-move blank entry reaches D at head 3 with a mark behind the head at cell 1; the complete right ray from head 3 is blank. Nine D/0 children have certificates:

| D/0 action | Certificate | Length | Shift |
|---|---|---:|---:|
| 0RD | fresh right ray | 1 | +1 |
| 1RD | fresh right ray | 1 | +1 |
| 1RE | fresh right ray | 2 | +2 |
| 0RA | fresh right ray | 6 | +4 |
| 1RA | fresh right ray | 6 | +4 |
| 1RB | fresh right ray | 5 | +3 |
| 0LB | translated finite support | 5 | +1 |
| 0LE | exact finite configuration lasso | 2 | 0 |
| halt | immediate halt at the five-move entry | 0 | — |

The 0LB macro clears the old mark and translates the finite support one cell right. The 0LE macro is an exact two-step D,E lasso. The halt child stops at the D/0 slot.

Each deeper child fixes six slots and has mass (25^6=244,140,625). Within each parent, the D/0 assignments are pairwise disjoint.

## Exact P4-audit arithmetic (draft until Lean acceptance)

The baseline is the P4-specific `agent27GraftedAudit` report, which already includes the E/0=1LC certificate. It is a separate grafted audit built on the same physical depth-four base as `depth4ResidualAudit`; the top-level global manifest has not yet been updated.

Baseline P4-specific report:

- decided: 40,570,837,402,343,750
- open: 19,033,807,373,046,875

Adding the seven new E/0 children gives:

- decided: 40,570,880,126,953,125
- open: 19,033,764,648,437,500

Adding the ten E/0=0LC / D/0 children gives:

- decided: 40,570,882,568,359,375
- open: 19,033,762,207,031,250

Adding the eleven E/0=0RD / D/0 children gives the final drafted P4-specific report pair:

- decided: 40,570,885,253,906,250
- open: 19,033,759,521,484,375

The added decided mass beyond `agent27GraftedAudit` is exactly
[
7\cdot25^7+19\cdot25^6=47,363,281,250,
]
and the final report still sums to (25^{12}=59,604,644,775,390,625). Including the pre-existing E/0=1LC child, the P4 grafted audit classifies 53,466,796,875 completions beyond the ungrafted global depth-four base. These are local exact cylinder counts, not a universal BB(6) upper bound or a complete P4 closure.

## Lean artifacts and acceptance boundary

- `P4ZeroLDCycle.lean`: finite lasso and `agent48P4ZeroLD_cover`.
- `P4EightChildGraft.lean`: seven new E/0 children and the existing 1LC graft.
- `P4DeeperFreshRay.lean`: ten D/0 children under E/0=0LC, including a left-ray and a halt child.
- `P4ZeroRDDeeperGraft.lean`: eleven D/0 children under E/0=0RD, including translated, exact-lasso, and halt children.
- `P4DeeperFreshRayReport.lean` and `P4ZeroRDDeeperGraftReport.lean`: exact report-pair and mass-conservation theorems.

Agent 6's 2026-11-24 static review covered the original 21-child draft's macro lengths, translations, fresh-tail conditions, and count arithmetic. The seven new D/0 children (left-ray, translated-cycle, fresh-ray, and halting cases) were derived in this invocation and still await Lean checking. Static review is not a Lean compile or a formal acceptance claim.

The local preflight was attempted with the supplied Lean 4.36.0-rc2 split archive using the requested reconstruction/unzip/version command. `container.exec` returned a tool-level `CAAS ClientError` before any shell output; `python.exec` likewise returned `ClientError`. No archive size, ZIP integrity, local Lean version, or source compilation was obtained in this invocation. This is an execution-environment blocker, not evidence that the archive is corrupt.

The focused `verify_p4_frontier_graft` input is part of the existing `.github/workflows/agent32-zero-path-global.yml`. Run 45354692563 compiled the shared dependencies and then failed at `P4ZeroLDCycle.lean:1` with `unknown module prefix 'BB6Coverage'`: Lean module imports must use flat file-module names, not the declaration namespace. The six P4 source imports now use their actual module paths. The next targeted run compiles the full dependency closure, all 32 cover/report axiom profiles, and rejects `sorryAx` or `native_decide`.

After source acceptance, Agent32 still needs to graft these certificates into `ResidualFrontierManifest.lean`; this P4-specific audit is not yet the global report. The global manifest remains unchanged.

No universal six-state upper bound, BB(6) exact value, or complete decision of the P4 parent is established.
