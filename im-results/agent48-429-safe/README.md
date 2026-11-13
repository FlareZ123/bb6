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

## Full-tape lift and root suffix composition

Two follow-on modules now carry the source certificate into the physical
machine model:

- `RootNoFatalPhysical.lean` uses the existing
  `BB429PhysicalBridge.source_run_rep` to lift the blank-root run and every
  prefix to the complete bi-infinite tape. Its theorem
  `BB429RootNoFatalPhysical.root_prefix_no_fatal_physical` excludes the
  physical C/01 condition at every absolute time through 9,243.
- `RootNoFatalChain.lean` feeds that endpoint directly into the existing
  `BB429RootOuterLow42NoFatal.blank_root_outer_low42_no_fatal` theorem. It
  composes the 3,398-step outer-safe suffix (no C/0 at all) and 1,077-step
  low42 suffix (no C/01) to obtain
  `BB429RootNoFatalChain.blank_root_no_fatal_to_junc136`: the genuine blank
  root reaches a configuration represented by Junc(0,0,136) at step
  **13,718**, and every physical prefix through that endpoint avoids C/01.

The 13,718-step statement is a finite prefix certificate, not an
all-time invariant or a nonhalting proof. The next root-connected task is
to compose the regular Junc path from Junc(0,0,136) to Junc(45,0,58), then
attach the low-even r=32 branch. Do not re-simulate the first 13,718 steps.

## Verification

The 9,243-step root run and exact C/0 census were preflighted with Lean
4.36.0-rc2 using the exact source transition/zipper definitions, guard,
and source `ones`/`pairs01` constructors. Both `by decide` certificates
and the all-prefix guard theorem compile; the root run and event census
have axiom report `[propext]`, with no `sorryAx`.

The physical-lift and 13,718-step composition proof bodies were separately
type-checked against interface harnesses for the repository's existing
`source_run_rep` and outer/low42 suffix theorem signatures. This is a
proof-script preflight only, not a substitute for compiling the actual
import graph. The standalone workflow
`.github/workflows/agent48-429-no-fatal-guard.yml` now compiles the actual
source imports and audits the three source declarations. The physical and
composition modules still need to be appended to an existing full-source
workflow (the Agent 6 low42 workflow already builds their dependencies)
and compiled there. Until that run passes, the 13,718-step physical claim
remains a checked proof candidate rather than CI-certified evidence.
