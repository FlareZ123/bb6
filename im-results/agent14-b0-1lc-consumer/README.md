# B0=1LC cross-route consumer pilot

This directory contains two complementary proof-consuming interfaces for the
same difficult six-state, two-symbol research frontier. These are intermediate
research artifacts, **not an exact BB(6) result**.

## Lean: 65 side-witness graft into the 109-roster parent

- `Agent14B01LCGraft.lean` imports the exact B0=1LC parent and the 65
  accepted `SideWitness` certificates selected by
  `Root109Membership.lean`.
- Each certificate is lifted from `WeightedBound 7014` to any
  `WeightedBound B` with `7014 ≤ B`.
- The certificates are grafted sequentially using `FrontierAudit.addCertificate`.
  The resulting audit is exhaustive and mass-conserving: every completion of
  the parent is either certified at B or remains in the explicit open
  complement.
- The open-complement theorem states exactly that a parent completion remains
  open iff it matches none of the 65 selected witness cylinders.
- The parent has 10 free slots, hence mass `25^10`, and is an exact member of
  the retained 109-entry roster.
- `Agent14B01LC109Graft.lean` lifts this one-parent audit into the global
  champion-score interface: 108 other residual entries remain unchanged, and
  the former B0=1LC entry is replaced by the audit's explicit open complement.
  A conditional full-root Cover theorem is provided; it still requires all 108
  other residuals and closure of the audit complement.

The Python analysis in
`im-results/agent13-cross-route-pilot/analyze_b0_1lc_sidewitness_cover.py`
reports an exact finite-cylinder union count of 4,477,340,035,625 for the 65
side witnesses. Treat this as reproducible computation, not yet as a Lean
numeric theorem. The parent space is 95,367,431,640,625 completions. The
remaining complement is therefore still substantial.

## Coq: consume the exact held FARv3 source-queue node

- `Agent14HeldQueueConsumption.v` imports the source-side checkpoint proof
  `Agent42HeldCheckpointMembership.v` and the packed global-upper consumer
  `Agent5ChunkCoverage.v`.
- It filters only exact matches of the recovered held table
  `1RB0RD_1LC1LB_0LE1RA_0LC0RA_1LF1LD_1RD---` from an adaptive obligation
  list. Every removed match is safe at every bound by the original FARv3
  source theorem.
- A generic `Forall` equivalence proves that the full list is safe iff the
  filtered residual list is safe. The two filters form an exact partition;
  the checkpoint membership theorem proves the consumed part is nonempty.
- The packed global-upper theorem is specialized so chunk 28 may use this
  filtered residual list, while all other 128 chunks retain their original
  full obligations. A further theorem identifies the exact packed chunk-28
  residual with the `q_i(2800,100)` checkpoint at fuel 1,000,000 and
  continuation `AP_stop`.

This is a conservative exact-table filter: strict refinements of the held
partial table are intentionally retained in the residual complement. No
other active or held source node is discarded.

## Verification status

At the time of writing, the Lean consumer and the Coq consumer are awaiting
their dedicated CI compilation. The Coq transition-serializer injectivity
proof required a left-associated product destruct; the corrected pattern is
now in `Agent42HeldCheckpointMembership.v`. The dedicated Coq workflow target
`enumerate62-held-checkpoint-consumption` has been added but not yet run.

Two independent Lean FAR encodings on the held table found no certificate in
DFA sizes 6–10: both composition-based and implications-based searches returned
UNSAT at sizes 6–7 in both orientations and UNKNOWN/timeout at sizes 8–10 in
both orientations. This excludes only the completed solver instances, not
larger automata or other certificate forms. A follow-up composition search for
DFA sizes 11–12 is running.
