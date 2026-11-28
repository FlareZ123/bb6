# F321: exact logarithmic high-branch accelerator and halting-gate arithmetic

**Status:** source-derived elementary arithmetic and a reproducible BigInt experiment, not a Lean-accepted original-machine nonhalting theorem and not a Raw132 Cover. Literal machine: `1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`, historic F321, with A1 undefined. Its blank-run counter seed after 70 ordinary steps is `(a,d)=(1,1)`.

**Source:** [google-deepmind/cryptids, pinned F321 Lean reduction](https://github.com/google-deepmind/cryptids/blob/c86f15861709b76042998c5211c7b2f83991621b/BusyBeaver/BB6/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean). The upstream `HasCollatzReduction` and `IsValidAcceleration` prove a reduction, not an orbit decision. The [source crosswalk](../agent24-upstream-census/README.md) confirms the rooted RLE match.

## Exact bulk theorem

The published counter map `T` has the high branch `(a,d) -> (a-d-2, 2d+3)` when `a>=d+2`. For nonnegative `a,d,j`, put
```
D_j = (d+3) 2^j - 3
A_j = a - (d+3)(2^j - 1) + j
Delta_j = A_j-D_j = a+d+6+j - (d+3) 2^(j+1)
```
If `Delta_i>=2` for each `i<j`, then the next `j` counter-map transitions are **exactly** `(a,d)->(A_j,D_j)`. Induction uses `D_(j+1)=2D_j+3` and `A_(j+1)=A_j-D_j-2`. Since `Delta_(j+1)-Delta_j = 1-(d+3)2^(j+1) <= -5`, there is a unique first exit index `J=min{j:Delta_j<=1}`. Exponential doubling and exact-integer binary search find `J` in `O(log(J+1))` BigInt shifts/comparisons, instead of executing each high transition. The output pair is nonnegative.

The high-run exit has a **complete dyadic chamber partition**. At fixed `d`, the integers `a>=0` are partitioned into disjoint consecutive intervals
```
I_j(d) = [L_j,U_j],  j=0,1,2,...
L_j = (d+3) 2^j - d - 3 - j
U_j = (d+3) 2^(j+1) - d - 5 - j.
```
Indeed `L_0=0` and `L_(j+1)=U_j+1`. An input `a in I_j` takes **exactly j high steps** and exits at `(r,D)=(a-L_j,(d+3)2^j-3)`; here `r` ranges bijectively over every integer `0<=r<=D+1`. The *sole* halting value in each chamber is the upper endpoint `a=U_j` (`r=D+1`). Since `U_j>=2^j`, among all `0<=a<=N` with a fixed `d`, at most `1+floor(log2 N)` values can halt before the next nonhigh transition, for `N>=1`. This density-zero **one-burst** statement does not control repeated epochs.

There is also a **complete finite inverse** of the maximal high-run map. Given `(r,D)`, a predecessor exists only when `0<=r<=D+1`. For each `j>=0` with `2^j | (D+3)` and `(D+3)/2^j >=3`, the unique predecessor in chamber j is
```
d = (D+3)/2^j - 3
a = D - d - j + r.
```
There are no others, hence at most `v2(D+3)+1` preimages (only one when `D+3` is odd). `inverseBulkHigh` implements this exact finite, 2-adic inverse and exhaustively tests it against the forward map on the 4,000 small starting pairs. This is an actionable inverse-ancestry interface for the F321 reachability problem.

The **exact halting gate at first exit** is:
```
a+d+5+J = (d+3) 2^(J+1).
```
When the incoming `a=4u+6` (the output of either `a<d` branch), halting requires `d+J≡1 (mod 4)`. For `J>=1`, reduce the equation modulo 4. For `J=0`, `a=d+1` and `a≡2 (mod 4)` imply `d≡1 (mod 4)`. Consequently incoming `d=1` demands `J≡0 (mod4)`, and `d=2` demands `J≡3 (mod4)`. These conditions are necessary, not sufficient.

For every nonhalting counter-map transition the parameter sum `a+d` **strictly increases**: by 1 in the high branch; by 5 if `a=d` (new pair `(2a+4,1)`); by 6 if `a<d` and `d>=3a+1` (new pair `(4a+6,d-3a)`); and by at least 8 in the middle `a<d<3a+1` branch (new pair `(4a+6,b)`, `b=2` when `d-a` even and `b=1` otherwise). In the middle case `d<=3a`; equality forces `b=2`, otherwise `d<=3a-1`. Thus no wholly live counter orbit is periodic; this does **not** rule out future halting.

## Executable evidence and limitations

`node f321-bulk.cjs 100000` runs an exact BigInt implementation. The independent direct and bulk high calculations agree on all 4,000 pairs with `0<=a<100, 0<=d<40`, three enormous cases and the first 500 authentic epochs; strict growth is tested on those 4,000 pairs. The arithmetic is derived from, but does not independently authenticate, the original Lean Turing-machine reduction.

From `(1,1)`, **100,000 complete nonhalting counter epochs** (a maximal high run plus one nonhigh branch) correspond to **953,789,045 individual counter-map transitions** without a halt, ending at a counter of at most 33,436 binary digits. Nonhigh branch counts: equality 1, far 42,890, middle 57,109; longest high run 33,433. A 30,000-epoch checkpoint gave 84,657,074 counter transitions and 9,956-bit counters. These are *not primitive TM transitions*, and this finite experiment does not establish BB(6), F321 nonhalting, or any physical-machine step lower bound. The strictly increasing sum makes the finite prefix imply an **all-future terminal-parameter exclusion**: because the larger final counter has 33,436 bits, `a+d>=2^33435` at that point. Any later halting gate `a=d+1` must therefore have `2d+1>a+d>=2^33435`, hence **`d>=2^33434`**. In other words, conditional on the exact numerical trace and upstream counter reduction, halts with terminal parameter `d<2^33434` are excluded for the entire blank orbit, not merely within the simulated prefix. This is a computation-assisted parameter cutoff, **not** an infinite-orbit decision.

**Next proof edge:** find and formalize a source-faithful invariant of the nonhigh return map forbidding the exact first-exit equality for **every** reachable pair, or construct a reached halt. A Lean proof of the bulk formula would be a valuable starting point for a verified accelerated orbit checker; until then it is a paper-level derivation backed by independent arithmetic tests. F197 is a different Raw132 leaf and does not decide F321.
