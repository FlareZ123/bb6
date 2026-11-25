# Six-hole raw117 and raw112 siblings: source-checked progress

Both parents extend the same first-one root path and differ only in the transition at E1=(4,true). Each has six holes and exactly 25^6 = 244,140,625 compatible full tables. Keep the labels explicit: **E1=1RD (raw117)** and **E1=1LC (raw112)**. Other projects also use the index “112” for unrelated residuals.

## E1=1RD (raw117): complete source-accepted cylinder

Parent table:
`1RB---_1RC---_0RD---_1LD1RE_---1RD_------`

- Exact weighted bound: **1,291**; an attaining completion halts at weighted score 1,291.
- Original-source Lean audit: [CI 45561386072](https://github.com/FlareZ123/bb6/actions/runs/45561386072), head `988705d0e0d7de1b736777b1b66b324115d75fdb`.
- All six disjoint child shards and the final assembly passed.
- The assembly checked `all117`, `attained117`, `exact117`, `canonical_cut_count`, `cut_sound`, `canonical_cut_sound`, and `cover_at_target`. The axiom gate allowed only `propext`, `Classical.choice`, and `Quot.sound`; it rejected `sorryAx` and `native_decide`.
- The exact parent matches raw residual index 117 / canonical index 81 in `canonical-124.json`. The Lean quotient theorem removes exactly one entry from the 96-entry canonical remaining roster (96→95).

This is a complete theorem for one six-hole cylinder, not a global BB(6) upper bound.

### Canonical integration opportunity

The sibling E1=0LD (raw114, canonical index 79) is already source-accepted at weighted bound 7,014 and appears in the current canonical 77-roster. Raw117 is the distinct E1=1RD sibling. The proposed composition is now written in [Canonical76Raw114Raw117.lean](Canonical76Raw114Raw117.lean): it imports `CanonicalRaw114Accepted` and `Raw117CanonicalCut`, filters the raw114 77-roster by the raw117 cylinder, and states the exact `roster.length = 76` count, mixed-bound soundness, and champion-score exactness consumer. This module is not yet source-compiled; it has been sent to Agent31 for inclusion in the manifest-compatible CI build. Do not report 76 until the exact count, sound theorem, and target-B consumer pass.

## E1=1LC (raw112): two independent partial classifications, no complete parent closure yet

Parent table:
`1RB---_1RC---_0RD---_1LD1RE_---1LC_------`

This is raw residual index 112 / canonical index 77 in `canonical-124.json`.

### Agent 8 exact leaf classification

The deterministic checkpoint is in `discover.py` and `raw112_checkpoint.py`. Its exact partition is:

| Class | Count |
|---|---:|
| Open leaves | 13,289 |
| FAR, original bank | 12,896 |
| Additional FAR, extra bank | 115 |
| One-block symbolic candidates | 215 |
| Two-block symbolic candidates | 23 |
| Late first-hole queries | 6 |
| Remaining hard leaves before the eight inductions | 34 |

Thus 13,011 leaves are FAR, with 215 one-block, 23 two-block, 6 late-query, and 34 hard leaves remaining. Eight of those 34 now have universal nonhalting inductions **accepted against the original source** in [CI 45561514651](https://github.com/FlareZ123/bb6/actions/runs/45561514651): IDs 10554, 12597, 2124, 7885, 4710, 6043, 12495, and 56. The source target compiled `Raw112Binary`, `Raw112Quinary`, `Raw112Alternating`, `Raw112Unary`, and all four generated `Raw112MultiSweep` modules, with no `sorryAx/native_decide`. **26 hard leaves remain.**

The largest observed actual first-hole query is at ordinary time 91,502. Consequently, a 7,014 or 980 bound is false for this parent; the parent audit needs a bound at least 91,503. Use 100,000 as the current safe audit target.

Details and exact recurrence proofs: [Raw112BinaryCounters.md](Raw112BinaryCounters.md), [Raw112Alternating.lean](Raw112Alternating.lean), [raw112_multisweep.py](raw112_multisweep.py), and [raw112_checkpoint.py](raw112_checkpoint.py).

### Agent 47 partial-audit alternative

`im-results/agent47-raw112-cut/generate.py` uses the same parent and the same open-list SHA, but a different FAR bank and symbolic/inductive certificate library. Its current generated draft covers 12,723 FAR leaves and 564 further symbolic/inductive leaves, leaving exactly **two residual leaves** in a `PartialAudit` at weighted bound 100,000. The generated theorem is intended to establish
`WeightedBound 100000 m ∨ ∃ e ∈ residuals, compatible e.2 m`
with `residuals.length = 2`.

This is currently a draft, not yet original-source accepted and not a complete parent bound. The exact two residual tables and a 100-million-step empirical prefix study are preserved in [Agent47Raw112Residuals.md](Agent47Raw112Residuals.md). Neither residual reads its remaining F0 hole during that prefix, so all 25 F0 completions share it; this is evidence for a recurrence investigation, not a nonhalting proof. Source-audit run 45575393941 generated the files but the GitHub runner shut down at 08:35:47Z while compiling `Raw112Sparse30Row10` (no Lean diagnostic). The workflow has been adjusted to four compile workers and a 120-minute timeout, with artifact upload on failure, and has been dispatched again. Do not call the partial theorem source-accepted until the retry passes. The exact two residuals must then be resolved to close the parent.

## Reproduction and scope

- Raw117 discovery: `python im-results/agent8-tnf-raw117/discover.py 117 --sweeps`; source-accepted closure: CI 45561386072.
- Agent8 raw112 leaf classification: `python im-results/agent8-tnf-raw117/discover.py 112`, then `python im-results/agent8-tnf-raw117/raw112_checkpoint.py`; source-accepted eight-leaf audit: CI 45561514651.
- Agent47 raw112 partial audit generator: `python im-results/agent47-raw112-cut/generate.py`; original-source closure pending the new workflow.

Neither sibling closes the whole canonical frontier. The global BB(6) upper bound and exact value remain open.


## Canonical E1 sibling composition: 72-roster draft

The six distinct E1 siblings raw107, raw113, raw114, raw115, raw117 and raw119 have a written quotient-roster composition in `Canonical72Raw107Raw113Raw114Raw115Raw117Raw119.lean`. Its current champion-coupled imports are unsuitable for independent source acceptance, so the parallel `Canonical72RosterOnly.lean` separates the roster layer from the champion score wrapper.

The roster-only interface is:

- exact `roster.length = 72` by `decide`;
- a source-rooted dichotomy at weighted bound **7,014**, with the six discharged parent cylinders removed and all retained quotient-compatible entries explicit;
- generic `exact_at_target` for any (B\ge 7014), with all 72 residual `Cover` premises and an attaining blank-start witness explicit;
- no import of `Canonical77ExactComposition` or `TM63RawUpperInterface`.

This is still an intermediate draft. The required dependencies are not yet jointly source-accepted:

- raw107 parent closure: source-accepted, [CI 45533196624](https://github.com/FlareZ123/bb6/actions/runs/45533196624);
- raw114 parent closure and canonical77 base: source-accepted, [CI 45554648116](https://github.com/FlareZ123/bb6/actions/runs/45554648116);
- raw117 six-hole cylinder and canonical cut: source-accepted, [CI 45561386072](https://github.com/FlareZ123/bb6/actions/runs/45561386072);
- raw113 exact parent: audit pending in [CI 45628984219](https://github.com/FlareZ123/bb6/actions/runs/45628984219);
- raw115/raw119 sibling audit: pending in [CI 45628975402](https://github.com/FlareZ123/bb6/actions/runs/45628975402); earlier run 45581575103 was cancelled before compilation completed;
- the champion-independent raw107+raw114 roster base and the new 72-roster consumer still require a joint Lean source/axiom audit.

The next integration should compile `CanonicalTwoParentRosterOnly` first, then `Canonical72RosterOnly` against the accepted raw117, raw113, raw115 and raw119 source closures. The exactness theorem remains conditional: even after the roster proof is accepted, BB(6) is not determined until all 72 retained Covers are established at the champion score. Do not report 72 as an accepted global frontier or as an upper bound.
