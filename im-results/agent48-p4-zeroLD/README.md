# P4 exact child grafts: finite lasso and fresh-ray certificates

**Status:** 21 new disjoint source-cylinder certificates are drafted for the P4 depth-four parent. The Lean modules and exact report theorems are **not yet accepted**: this invocation could not run a local preflight, and the focused CI gate has not yet been dispatched. Keep this work in `im-results/`.

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

Two additional E/0 branches admit useful D/0 refinements.

### E/0 = 0LC

The six-move blank entry A/0, B/0, C/1, D/1, E/0, C/1 clears the tape and reaches D at head 2 on a blank tape. Eight D/0 children have source certificates:

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

The translated checks compare the entire finite marked-cell support; they do not assume every intermediate head stays to the right of the entry head.

### E/0 = 0RD

The five-move blank entry reaches D at head 3 with a mark behind the head at cell 1; the complete right ray from head 3 is blank. Six D/0 children have fresh-ray certificates:

| D/0 action | Macro | Length | Shift |
|---|---|---:|---:|
| 0RD | D | 1 | +1 |
| 1RD | D | 1 | +1 |
| 1RE | D,E | 2 | +2 |
| 0RA | D,A,B,C,D,E | 6 | +4 |
| 1RA | D,A,B,C,D,E | 6 | +4 |
| 1RB | D,B,C,D,E | 5 | +3 |

Each deeper child fixes six slots and has mass (25^6=244,140,625). Within each parent, the D/0 assignments are pairwise disjoint.

## Exact frontier arithmetic (draft until Lean acceptance)

The existing global report before these P4 refinements is:

- decided: 40,570,837,402,343,750
- open: 19,033,807,373,046,875

Adding the seven new E/0 children gives:

- decided: 40,570,880,126,953,125
- open: 19,033,764,648,437,500

Adding the eight E/0=0LC / D/0 children gives:

- decided: 40,570,882,080,078,125
- open: 19,033,762,695,312,500

Adding the six E/0=0RD / D/0 children gives the final drafted report pair:

- decided: 40,570,883,544,921,875
- open: 19,033,761,230,468,750

The added decided mass is exactly
[
7\cdot25^7+14\cdot25^6=46,142,578,125,
]
and the final report still sums to (25^{12}=59,604,644,775,390,625). These are local exact cylinder counts, not a universal BB(6) upper bound or a complete P4 closure.

## Lean artifacts and acceptance boundary

- `P4ZeroLDCycle.lean`: finite lasso and `agent48P4ZeroLD_cover`.
- `P4EightChildGraft.lean`: five fresh-ray children and one halt child, added to the existing 1LC graft.
- `P4DeeperFreshRay.lean`: eight D/0 children under E/0=0LC.
- `P4ZeroRDDeeperGraft.lean`: six D/0 children under E/0=0RD.
- `P4DeeperFreshRayReport.lean` and `P4ZeroRDDeeperGraftReport.lean`: exact report-pair and mass-conservation theorems.

Agent 6's 2026-11-24 static review found the listed macro lengths, translations, fresh-tail conditions, and count arithmetic consistent with the source drafts. That review is not a Lean compile or a formal acceptance claim.

The local preflight was attempted with the supplied Lean 4.36.0-rc2 split archive using the requested reconstruction/unzip/version command. `container.exec` returned a tool-level `CAAS ClientError` before any shell output; `python.exec` likewise returned `ClientError`. No archive size, ZIP integrity, local Lean version, or source compilation was obtained in this invocation. This is an execution-environment blocker, not evidence that the archive is corrupt.

A focused `verify_p4_frontier_graft` input has been added to the existing `.github/workflows/agent32-zero-path-global.yml` rather than creating another workflow. It compiles the existing five-slot dependency closure, all six P4 modules, all 25 cover/report axiom profiles, and rejects `sorryAx` or `native_decide`. One targeted run is the fallback diagnostic for this unavailable local preflight. After source acceptance, Agent32 still needs to graft these certificates into `ResidualFrontierManifest.lean`; this P4 work is not yet part of the global report.

No universal six-state upper bound, BB(6) exact value, or complete decision of the P4 parent is established.
