# Authentic weighted-TNF pilot

A complete normalized subtree at cut 6, reached from `firstOneCylinder` by nine genuine first-hole refinements, has an exact local weighted threshold of 84 by the explicit finite-replay argument below. [TNFPilot.lean](TNFPilot.lean) constructs the actual `FirstHolePath` and `WeightedTNFCertificate` proof objects using the unmodified source interfaces. **Full original-source compilation passed** in [manual run 45405148454](https://github.com/FlareZ123/bb6/actions/runs/45405148454), at commit `20db4dbe086ea0e6436eacbb5fab725957d3bda2`; the dedicated step ran successfully, including the standalone replay and fail-hard axiom-output guard against `sorryAx` and `native_decide`. This is an intermediate integration pilot, not a universal BB(6) bound.

## Certificate

Parent table: `1RB---_1RC1LF_0RD0RB_1LD1RE_---0LB_0LE0LA`.

The authentic path (ordinary moves, queried slot, assigned action) is:

| moves | slot | action |
|---:|---|---|
|1|B0|1RC|
|2|C0|0RD|
|3|D0|1LD|
|5|D1|1RE|
|6|E1|0LB|
|7|B1|1LF|
|8|F1|0LA|
|11|C1|0RB|
|21|F0|0LE|

All six labels are introduced in canonical order. The first hole at the parent is A1 at time 31, head -1 and ones {-1,1,3,4,6}. The halt sibling has raw score 32, with possible incoming delays [0,1,2], so weighted score at most 34. The other hole is E0.

Every ordinary A1 branch has one of the following certificates. A last-hole witness is the time of its first E0 query; E0=halt scores n+1 and the other 24 E0 assignments are total ordinary tables. A ray witness reaches D with an entirely blank left half-line and D0=1LD. A lasso repeats the exact state, absolute head, and finite tape set.

| A1 | verdict | time | earlier repeat |
|---|---|---:|---:|
|0LA|last|36| |
|0LB|last|40| |
|0LC|ray|33| |
|0LD|ray|32| |
|0LE|last|32| |
|0LF|last|33| |
|0RA|lasso|40|20|
|0RB|lasso|52|20|
|0RC|last|34| |
|0RD|ray|32| |
|0RE|last|32| |
|0RF|last|33| |
|1LA|last|83| |
|1LB|last|68| |
|1LC|last|34| |
|1LD|ray|32| |
|1LE|last|32| |
|1LF|last|33| |
|1RA|lasso|33|29|
|1RB|lasso|36|20|
|1RC|last|34| |
|1RD|last|37| |
|1RE|last|32| |
|1RF|last|42| |

The 16 last-hole halters all set E0=halt, which excludes every nonzero incoming zero-prefix delay: no read-zero row can lead to A. Thus their exact weighted scores equal their raw scores; the maximum is 84 (A1=1LA, E0=halt). There are 625 raw completions in the parent cylinder: 25 from A1=halt, 16 last-hole halters, and 584 nonhalters (16×24 + 8×25). No residual child is discarded. The full branch has one expand node, 16 lastHole nodes and eight nonhalt nodes. The 25 root-halt completions are handled by the expand weight proof.

## Reproduction and acceptance

Run `python replay.py` in this directory to independently replay the authentic path, every witness, and the exact incoming-delay sets. The script checks finite evidence, not Lean proofs. The Lean module uses kernel `decide` for the same finite predicates and the repository's existing sound last-hole, lasso, ray and weighted-TNF rules. Its exact source closure compiled under Lean 4.36.0-rc2 through the existing manual coverage workflow's `weighted-tnf-pilot` target. The module prints the axiom profiles of all six principal exported declarations, and the workflow rejects `sorryAx` or `native_decide` in the captured compilation output. The successful-job log itself was not retrieved, so the precise printed profile beyond that guard is not independently asserted.

The source checkout failed locally with DNS resolution of github.com, although the uploaded Lean 4.36.0-rc2 toolchain extracted and ran successfully. The existing manual closure runner provided the accepted original-source check; no new standalone workflow was created. The entire root-to-parent path's other siblings remain outside this pilot. It is a genuine local integration slice, not a closed authentic root or the full upstream queue schedule.
