# Incidence quotients of two-sided automata (Agent4, 2026-11-26)

For one stack side, let S(x) be the set of triples (control, scanned bit,
opposite stack state) occurring with stack state x in the finite joint
invariant. Merge states with identical S(x), mapping original state zero to
class zero. Project all inverse edges and the joint relation; for each class
and written bit select the original push of its least-numbered representative
and project the target.

Why this preserves closure: for a push on the merged side, any represented
joint state can use that class representative because their incidence sets are
equal. Its original push and every opposite-side pop successor are valid,
hence their projections are valid. For a pop on the merged side, each
projected pop edge comes from some class member; identical incidence implies
that member had the same joint configuration with the opposite state and
control. Its original successor projects to the required successor. The
blank loops and initial configuration project unchanged. Alternate sides
until neither side shrinks. The candidate optimization is untrusted;
the existing exact Lean checker decides the resulting certificate.

## Reproduction and results

Run `python im-results/agent4-two-sided-automata/bench_quotient.py`.
All 19 original symmetric-parameter Raw58 RLE witnesses passed both original
and quotient closure tests in Python. The rows below are counts of joint
configurations before and after (not machine counts):

| Child / leaf | Before | After |
|---|---:|---:|
| 0LE/203 | 8723 | 2560 |
| 0LF/57 | 222 | 60 |
| 0LF/293 | 193 | 113 |
| 0LF/313 | 217 | 125 |
| 0LF/480 | 473 | 205 |
| 0LF/1061 | 507 | 225 |
| 1LE/641 | 3084 | 338 |
| 1LE/750 | 510 | 215 |
| 1LE/751 | 831 | 196 |
| 1LE/752 | 1564 | 285 |
| 1LF/131 | 1585 | 173 |
| 1LF/133 | 2098 | 215 |
| 1LF/134 | 1513 | 161 |
| 1LF/136 | 2178 | 224 |
| 1LF/197 | 87 | 84 |
| 1LF/250 | 226 | 86 |
| 1LF/560 | 275 | 158 |
| 1LF/831 | 72 | 38 |
| 1LF/1186 | 3084 | 338 |

The literal LE203 table is
`1RB0LE_1RC1RA_0RD---_1LD1RE_1LF0RA_1RC0LF`.
Its stack sizes decrease 87/348 -> 72/100. I recovered the exact original
Raw109 closure artifact 15035255805 (435 modules; verified source/object
hashes and compiler binary hash). TwoSidedAutomata.lean at Git blob
c04bf81e19d55b3d028c714e628246a4b917f03c compiled against that core with
the official supplied Lean 4.36.0-rc2. The compressed LE203 cert was emitted,
its 12 row lemmas compiled as separate modules, and the final assembled
`BB6.Agent4Raw58LE.M203.checked` and `never` compiled locally:
`checked` uses propext and Quot.sound; `never` additionally
Classical.choice. No sorryAx/native_decide.

The current Raw58 generator enables the quotient only for LE and LF1; leave
the already dispatched LF shards on their unchanged certificate representation
and do not unnecessarily rebuild source-accepted LE1. The Boolean seed
lemmas must have Bool equality types for the direct rw assembly, as verified
in the compressed certificate. This is a source-checked leaf certificate,
not a complete child/parent Cover. No roster count changes.

## Chunked packed-row alternative

The exact Lean module [PackedStackAutomata.lean](PackedStackAutomata.lean) uses independently checked numeric bitmaps and chunked sparse rows. It proves the bitmap membership equivalence, extracts the particular checked chunk from membership, and proves the same stack preservation and original-machine never theorem. The source was checked locally against the pinned original core. The compressed LE203 leaf compiled through all twelve 64-entry-chunk row modules and final checked/never with ordinary axioms only. The hardest row (q=5,a=true) measured 16.29 s / 1,242,524 KB peak RSS for the packed chunked version versus 27.26 s / 3,231,496 KB for the trie row with rfl (same local compiler, certificate and source core; proof tactics differ). The unchunked packed row took 23.41 s / 3,105,164 KB; chunking is responsible for most memory improvement. Generated packed data size is around 41 KB versus 194 KB for the compressed trie. Reproduce via emit_packed.py, which writes data, twelve row modules, and the final proof. The production Raw58 generator continues to use the compressed trie route pending need for this alternative.
