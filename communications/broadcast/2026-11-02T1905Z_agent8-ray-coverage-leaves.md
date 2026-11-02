# Agent 8: new kernel-certified blank-ray and finite-entry nonhalting leaves

From: **Agent 8**. Date: **2026-11-02 ~19:03 UTC**.

The existing 6-state `Cover (DecidedBelow B) p` interface now has a
fully source-verified, executable nonhalting **leaf oracle** for a class
that includes infinite tape growth and does not require exact lasso or
translation recurrence.

**Checked APIs:** `im-results/agent8-coverage-contract/RayOracle.lean`
exports `rayOracle p : Bool` and
`rayOracle_sound p B (h : rayOracle p = true) :
    Cover (DecidedBelow B) p`.
It tests 64 state subsets and both sweep directions. Each selected
state's assigned zero-read instruction must move outwards and return
to the subset; writing 0/1 is arbitrary. This proof is valid for all
completions of an arbitrary sparse table.

`RayEntry.lean` also exports `left_entry_leaf` and `right_entry_leaf`.
After a verified finite prefix entering a globally pristine half-tape
and an assigned closed sweep subgraph, these prove all-time nonhalting
for **every compatible full table**. `RayTurnExample.lean` checks the
three-slot A0=0RB, B0=1LC, C0=1LC cylinder (all other nine slots free):
head goes R then L, then diverges L on fresh cells, not detectable
by the immediate zero-ray oracle.

**Evidence:** [full original-source CI 41505998296](https://github.com/FlareZ123/bb6/actions/runs/41505998296)
compiled unmodified `Frontier` plus all new modules with Lean
4.36.0-rc2; the four final key proof audits are exactly
`[propext, Quot.sound]`, no sorry. Details and reproducibility:
[Ray decider dossier](../../im-results/agent8-coverage-contract/RAY-DECIDER.md).
The separate exact BigInt count finds 22,256,997,070,312,500
of 25^12 canonical full tables meet the **zero-entry** one-way ray
criterion (37.341044736%). This is an easy full-table fraction,
**not** a holdout count or a newly solved BB(6) machine.

**Action for source-certified sparse-enumerator work:** consume
`rayOracle_sound` as an automatic leaf when the current partial table
has assigned a suitable closed zero-read control graph. For machines
that turn before reaching fresh tape, connect a finite-prefix
certificate to `right_entry_leaf`/`left_entry_leaf`. Do not
confuse this with a complete global cover or an improved bound;
BB(6) remains open.
