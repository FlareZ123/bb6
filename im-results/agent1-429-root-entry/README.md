# Exact blank-root entry into the #429 J chart

## Candidate result

The source machine's blank A-root reaches the physical J(0,0) tape after
35 primitive transitions. An independent raw simulation gives:

- state A;
- absolute head coordinate 3;
- marked cells exactly `[-3,4] ∪ {6}`;
- equivalently, relative to the head, marked cells `[-6,1] ∪ {3}`.

This is the physical tape specified by the J-chart definition at (u=w=0).

`JRootEntry.lean` records the complete twelve-slot #429 table, including
the D/1 halt, and the ordered 35-write trace. It attempts to prove the
raw-run equality in `BB6Coverage.run`.

<badge color="warning">Lean CI not yet passing</badge>

The first CI attempts exposed an important modeling issue: the existing
`BB429PhysicalFrontier.target429` is a completion of an eleven-slot
*partial* table, not the concrete source machine. It cannot be used as a
computable full-table root trace. The current candidate therefore defines
the complete original table explicitly as `source429`. The proof still
requires a successful kernel check; do not treat the theorem as established
until the manual workflow passes.

## Why it matters

A successful check will connect the genuine blank root directly to the
canonical J(0,0) physical configuration. That supplies the base case for
the all-time J/Junc chart and global head-frontier argument.

## Remaining open problem

The 35-step entry alone does not prove that the subsequent J/Junc orbit
stays in a safe chart, that later C/0 events are global head records, or
that #429 never halts. The central remaining task is the all-time
physical frontier/history invariant across the complete J/Junc transition
family.

## Reproduction

Run `.github/workflows/agent1-429-root-entry.yml` manually under Lean
4.36.0-rc2. The workflow rejects any theorem depending on `sorryAx`.
