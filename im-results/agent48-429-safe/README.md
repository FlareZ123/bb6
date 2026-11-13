# #429 blank-root no-fatal prefix

## Established source-zipper theorem

The original six-state #429 zipper interpreter now has a kernel-reducing
finite certificate from the genuine blank zipper origin

`z 0 [] false []`

through 9,243 primitive transitions to the exact Junc(11,0,98) word

`z 0 (true :: (pairs01 11 ++ ones 5)) true
  (true :: (pairs01 0 ++ ones 98 ++ [false,true]))`.

The endpoint uses the repository's canonical `ones` and `pairs01`
definitions from `BB429SourceE1Return`; the displayed word is exactly the
`junc 11 0 98` definition in `BB429FinishScanEDelta`.

The decisive theorem is
`BB429RootNoFatalPrefix.root_prefix_no_fatal_source`:
`runNoFatal 9243 rootBlank = some rootEndpoint`.
The guard rejects only C/0 with a marked immediate right neighbor (C/01).
The imported `runNoFatal_prefix` theorem lifts this to **every** primitive
prefix, including the initial and final configurations:
`root_prefix_all_prefixes_nonfatal`.

## Exact C/0 census

The independent trace theorem
`root_czero_event_trace` gives every C/0 instruction start, its zero-based
primitive time, the head displacement from the blank origin, and the
immediate right-neighbor bit:

| Time | Head | Right neighbor |
| ---: | ---: | --- |
| 2 | 2 | blank |
| 13 | 5 | blank |
| 64 | 8 | blank |
| 111 | 11 | blank |
| 275 | 15 | blank |
| 366 | 18 | blank |
| 882 | 22 | blank |
| 981 | 25 | blank |
| 1820 | 28 | blank |
| 2682 | 32 | blank |
| 2913 | 35 | blank |
| 5430 | 38 | blank |
| 8548 | 42 | blank |
| 8953 | 45 | blank |

There are exactly 14 C/0 starts in the 9,243-step prefix, and all 14 are
C/0/blank-right. Thus the source zipper computation has no C/01 event on
this entire finite root segment. The endpoint is Junc(11,0,98), matching
the start state required by Agent 1's conditional 3,398-step outer-safe
plus 1,077-step low42 suffix.

## Proof boundary

This is a finite source-zipper result. It does **not** establish an
all-time invariant, nonhalting, or a BB(6) decision. This module does not
yet include the full-tape `Config` lift or compose the following 4,475
steps. The physical bridge should use the existing
`BB429PhysicalBridge.source_run_rep` and the already maintained
`BB429RootOuterLow42NoFatal.blank_root_outer_low42_no_fatal`; do not
reconstruct the source table or duplicate the guard.

## Verification

Both finite computations were preflighted with Lean 4.36.0-rc2 using the
exact source transition/zipper definitions, the no-fatal guard, and the
source `ones`/`pairs01` constructors. The kernel axiom reports were
`[propext]` for the root run and event census; the all-prefix theorem
uses the checked generic guard lemma. No `sorryAx` is introduced.

The manual/PR-scoped workflow
`.github/workflows/agent48-429-no-fatal-guard.yml` now compiles the actual
repository imports and audits all three root declarations. The updated
workflow has not yet produced a run for this addition; until then, the
repository-level import chain remains pending its CI check.
