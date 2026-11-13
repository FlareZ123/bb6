# Junc(0,w) return-map exploration

**Status:** exploratory deterministic simulation plus algebraic composition plan. This is not a Lean theorem and does not prove an infinite run.

## Observed return sequence

Starting from the prepared Junc state J(0,344), the original six-state transition table was simulated for 20,000,000 steps. The following Junc(0,w) checkpoints were observed (times are relative to the J(0,344) input):

| Step | w |
|---:|---:|
| 0 | 344 |
| 145,374 | 408 |
| 196,453 | 436 |
| 251,186 | 464 |
| 311,141 | 492 |
| 377,886 | 520 |
| 452,989 | 548 |
| 538,018 | 576 |
| 634,541 | 604 |
| 744,126 | 632 |
| 868,341 | 660 |
| 1,008,754 | 688 |
| 1,166,933 | 716 |
| 1,344,446 | 744 |
| 2,502,495 | 924 |
| 3,193,805 | 1,008 |
| 3,738,578 | 1,060 |
| 4,412,233 | 1,112 |
| 8,369,585 | 1,356 |
| 16,958,173 | 1,668 |
| 19,595,676 | 1,756 |

The simulation was continued to 20M steps without reaching a halt. Treat these as experimental observations only.

## Exact algebraic candidate for the repeated +28 branch

For w divisible by 4 with 408 ≤ w ≤ 736, define j=(w-360)/2 and k=(188-j)/2. Then j is even, k is a nonnegative integer, and j+2k+1=189, 2j=w-360.

The existing outer-safe macro formulas give:

1. Five outer-safe steps U=0,3,9,21,45, taking J(0,w) to J(93,w-171) in 11,139 steps.
2. One outer-safe step U=93, taking J(93,w-171) to J(189,w-360) in 35,553 steps.

The generic low42 endpoint formula for input J(j+2k+1,2j) then applies to J(189,w-360), and returns J(0,4j+4k+12)=J(0,w+28). Its source/physical step count is 4j²+22j+18k+79. Thus the full candidate return time is

T(w)=46,692+4j²+22j+18k+79
    =(w-360)²+13((w-360)/2)+48,463.

This predicts the observed sequence 408,436,464,492,520,548,576,604,632,660,688,716,744. At w=744, the formula gives j=192 and k=-2, so this low42 branch no longer applies; the observed next return is J(0,924), indicating a different regime.

## Physical return-map bridge

The canonical low42 physical result is now paired with a machine-level safety converse in this branch:

- `PhysicalNoFatalConverse.physicalC01_one_halts` proves directly from the original physical transition table that C/01 takes one step to D/1, after which `rawStep` is undefined.
- `PhysicalNoFatalConverse.physical_run_prefix_c01_free` proves that any successful physical run ending at a live, non-C/01 configuration is C/01-free at every primitive prefix.
- `Low42PhysicalNoFatal.low42_raw_head_all_c01_free` applies this to the canonical physical low42 run for every (j,k), using its represented Junc(0,0,4j+4k+12) endpoint.

These are Lean proof candidates pending the integrated manual workflow. They close the all-prefix C/01 gap for the canonical low42 physical run without lifting each prefix through the zipper.

The arbitrary-head wrapper is now formalized in `Low42PhysicalNoFatalAnyHead.low42_raw_head_any_c01_free`. It uses `JuncCanonical.represented_junc_eq_translatedJ` to identify a represented Junc with its translated canonical J configuration, and `RootShift.shift_run` to transport the complete physical run and every-prefix C/01 property. The new theorem preserves the exact endpoint head displacement. The integrated low42 workflow now includes the `High2PhysicalBridge` / `JuncCanonical` / `RootShift` dependency chain. The remaining return-map step is to compose this arbitrary-head low42 physical macro with the outer-safe physical segments.

The observed Junc(0,344) -> Junc(0,408) interval is 145,374 steps. It is not part of the 169,592-step blank-root theorem and remains a simulation observation, not a formal segment.

## NoFatal converse status

The source-level candidate `NoFatalRunConverse.runNoFatal_of_run_live` now formalizes the earlier sketch: an ordinary source run to a live, nonfatal endpoint is accepted by the guarded interpreter. The physical-level converse above establishes the corresponding all-prefix C/01 exclusion directly on `BB6Coverage.run`. Both proofs use the exact C/01 -> D/1 -> halt transition, and both remain pending Lean CI in the current integrated branch.

`Low43PhysicalNoFatal.low43_C0_record_all_prefix_c01_free` applies the physical converse to the generic low43 entry record: for every (v,k), the physical Junc-input -> C/0 checkpoint run is C/01-free at every prefix because its endpoint has scanned zero and a blank immediate right cell. This is intended to support the uniform C/0 continuation work being pursued by Agent 1.

## Formalized finite +28 return map

The experimental +28 branch is now represented by the Lean theorem
`BB429Junc0ReturnMap28.junc0_return_map_28` (pending the integrated manual CI run).

For every (12\le r\le94), from any physical configuration representing
`junc 0 0 (4*(r+90))`, the original six-state machine executes exactly

[
46692 + 4(2r)^2 + 22(2r) + 18(94-r) + 79
= 16r^2+26r+48463
]

steps to a physical configuration representing `junc 0 0 (4*(r+97))`.
Every primitive prefix of this physical run is C/01-free.

Equivalently, this proves the return map Junc(0,w) -> Junc(0,w+28) for every (w=4(r+90)), i.e. every multiple of four from 408 through 736 inclusive. The proof is not a simulation replay: it composes six parameter-uniform physical outer-safe returns (U=0,3,9,21,45,93; 46,692 steps) with the arbitrary-head low42 physical theorem at (j=2r,k=94-r). The generic physical NoFatal converse supplies the all-prefix C/01 exclusion from the live Junc endpoint.

In particular, twelve applications at (r=12,19,26,\ldots,89) give a formal path Junc(0,408) -> Junc(0,744), with total cost 1,199,072 primitive steps. The 12-step composition has not yet been packaged as a separate theorem. The subsequent Junc(0,744) -> Junc(0,924) segment and its 7,382-step Junc(381,3) -> Junc(387,2) gap remain unresolved.

## Second observed return family: J(11,w) -> J(11,w+32)

The 20M-step scan of the J(0,744) regime exposes a second repeated macro at J(11,w), for w=774,806,838:

1. Outer-safe U=11,25,53,109 takes J(11,w) to J(221,w-408) in 63,832 steps (individual costs 621, 2,777, 11,793, 48,641).
2. For the observed values, set N=(w-408)/2 and K=(221-N)/2. Then J(221,w-408)=J(N+2K,2N), so the generic low-even-4k endpoint formula returns J(11,4N+4K-2)=J(11,w+32).
3. The low-even-4k time is 4N²+22N+18K+261, so the full interval time is 64,093+4N²+22N+18K.

For w=774,806,838 the parameters are (N,K)=(183,19),(199,11),(215,3), and the predicted interval times are 202,417; 227,073; and 253,777. These exactly match the observed intervals J(11,774)->J(11,806)->J(11,838)->J(11,870). At w=870, N=231 and K=-5, so this low-even branch no longer applies. The observed path then goes through J(25,845), J(53,792), J(109,683), J(221,462), J(445,17), J(440,34), and returns to J(0,924).

As above, the endpoint/time algebra is suggested by existing macro formulas, but the combined parameterized physical/no-fatal theorem has not been formalized. The J(381,3)->J(387,2) transition preceding J(11,774) is also not yet identified/formalized; the listed intermediate Junc states are simulation observations.


## Observed w=744 to w=924 regime

The simulation's J(0,744)->J(0,924) interval (1,158,049 steps) decomposes at the observed Junc checkpoints as follows:

| Segment | Steps | Endpoint |
|---|---:|---|
| Outer U=0,3,9,21,45,93,189 | 191,493 | J(381,3) |
| Unidentified low-width transition | 7,382 | J(387,2) |
| Low-even-4k N=1,K=193 | 3,761 | J(11,774) |
| Three J(11,w)->J(11,w+32) cycles, w=774,806,838 | 683,267 | J(11,870) |
| Outer U=11,25,53,109,221 | 261,433 | J(445,17) |
| Low-odd v=8,n=217 | 5,306 | J(440,34) |
| Low42 j=17,k=211 | 5,407 | J(0,924) |

All endpoint/time values other than the J(381,3)->J(387,2) segment are explained by the existing outer-safe, low-even-4k, low-odd, and low42 macro formulas; the latter segment is presently only an observed simulation transition. The sum is exactly 1,158,049. This decomposition is a roadmap, not a proof: it still needs a formal physical lift for the generic macros and a theorem for the unidentified 7,382-step transition.
