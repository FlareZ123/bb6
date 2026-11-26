# Source-audited conditional 68-residual E1 parent reduction

**Status: accepted conditional Lean theorem; not a global BB(6) upper bound.** The exact six-state Busy Beaver value remains unknown.

## Result

The canonical76 quotient roster, already obtained after the source-accepted Raw107 and Raw114 parent cuts, can be reduced to a **68-entry residual roster** by consuming eight source-accepted parent cylinders in the common E1 sibling family.

The existing Canonical74 module first consumes Raw109 (E1=1RB) and Raw123 (E1=0RF), giving 76 → 75 → 74. The new Canonical68 consumer then proves exact sameTable membership for six more parents and applies empty-replacement grafts:

| Parent | E1 move | Parent bound | Original-source acceptance |
|---|---|---:|---|
| Raw60 | 1RA | 1,175 | [45686044022](https://github.com/FlareZ123/bb6/actions/runs/45686044022) |
| Raw109 | 1RB | 1,703 | [45633764095](https://github.com/FlareZ123/bb6/actions/runs/45633764095) |
| Raw110 | 0LC | 6,766,859 | [45597857116](https://github.com/FlareZ123/bb6/actions/runs/45597857116) |
| Raw111 | 0RC | 7,014 | [45568081544](https://github.com/FlareZ123/bb6/actions/runs/45568081544) |
| Raw117 | 1RD | 1,291 | [45561386072](https://github.com/FlareZ123/bb6/actions/runs/45561386072) |
| Raw121 | 1RE | 4,063 | [45616647230](https://github.com/FlareZ123/bb6/actions/runs/45616647230) |
| Raw123 | 0RF | 10,000 | [45700813110](https://github.com/FlareZ123/bb6/actions/runs/45700813110) |
| Raw125 | 1RF | 1,290 | [45722543448](https://github.com/FlareZ123/bb6/actions/runs/45722543448) |

The complete count chain is:

\[
76 \xrightarrow{\mathrm{Raw109}} 75
\xrightarrow{\mathrm{Raw123}} 74
\xrightarrow{\mathrm{Raw60}} 73
\xrightarrow{\mathrm{Raw110}} 72
\xrightarrow{\mathrm{Raw111}} 71
\xrightarrow{\mathrm{Raw117}} 70
\xrightarrow{\mathrm{Raw121}} 69
\xrightarrow{\mathrm{Raw125}} 68.
\]

Raw110 sets the common weighted-bound floor at 6,766,859. All smaller parent bounds lift to this floor.

## Formal statement and source audit

The new source module is [Canonical68E1ParentGraft.lean](../im-results/agent6-e1-parent-consumer/Canonical68E1ParentGraft.lean), with a reproduction and interface note in [its README](../im-results/agent6-e1-parent-consumer/README.md).

Its theorem sound68 proves that every root-compatible machine either satisfies WeightedBound 6766859 or is TNF-quotient-compatible with one of the 68 retained representatives. Its conditional exact_at_target theorem states that, for any B ≥ 6,766,859, exactness follows if:
1. the eight listed parent Covers are supplied (Raw109 is passed as its all-completions bound, matching the existing Canonical74 interface);
2. every one of the 68 retained quotient representatives has a Cover at B; and
3. a machine attaining B is supplied.

The new module intentionally takes the six additional Covers as explicit arguments instead of importing their large, heterogeneous source proof closures. The individual parent proofs are source-accepted in the runs listed above. This CI run validates the roster consumer and its conditional theorem, not a monolithic instantiation of all eight parent proofs.

The combined Canonical74 + Canonical68 source-audit job passed in [run 45725315357](https://github.com/FlareZ123/bb6/actions/runs/45725315357). It checked all six new exact membership-count theorems, the 73→68 roster lengths, sound68, and exact_at_target; the printed axiom profiles passed the explicit allowlist (propext, Classical.choice, Quot.sound) with no sorryAx or native_decide. The separate Canonical68 consumer artifact is artifact 15074083310; the same run also source-audited the Canonical74 dependency (artifact 15074083309).

## What remains open

The 68 retained Covers are still unresolved. The E1 sibling synthesis has 20 predicted entries: these eight accepted parents, eleven still-open sibling parents, and the champion-containing Raw113 entry. The new roster keeps all of those unresolved entries explicit; it does not silently discharge them.

The 6,766,859 floor is a coarse parent bound, not a claim that the current champion attains it. No global upper bound, exact BB(6) value, or maximality proof is established by this reduction. The mathematical contribution is the source-audited exact 76-to-68 quotient-roster reduction and its reusable conditional exactness interface.
