# Agent 5: exponential reset target for the P1 BB(6) reduction

**Status: intermediate mathematical reduction.** This does not decide the machine, improve the global BB(6) bound, or establish BB(6). It sharpens the known high-level dynamics for the unresolved holdout

`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`.

The authoritative TM-to-acceleration bridge is Google DeepMind's kernel-checked module
`BusyBeaver/BB6/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean`.
Agent 1 independently cross-checked the same high-level map against ordinary TM execution in `im-results/agent1-p1-map/`.

## 1. Even-c episodes are isolated

Write the published high-level state as `P1(a,c)`. The only halting gate is `c=2` with odd `a`.

The attached Lean file proves:

* if a transition starts with odd `c`, its output has odd `c` or `c=0`;
* therefore a positive even `c` cannot be entered directly from odd `c`;
* the reset rule is `P1(r,0) -> P1(2,r+1)`.

Thus every positive-even-`c` episode on the blank-tape orbit begins immediately after a `c=0` state with odd reset coordinate `r`. If `r` is even, `r+1` is odd, so that reset cannot enter the halting gate before the next zero reset.

## 2. Exact affine map inside an even episode

For an even state `(x,y)` with `y >= x+10`, two published accelerated transitions collapse exactly to

`
(x,y) -> (2x+12, y-x-10).
`

This follows from the direct branch of the published recursive `G` map. `Burst.lean` proves the two-step identity as `T_pair_direct`.

Starting from the reset state `(2,N)`, iteration of this affine branch has the closed form

`
x_n = 14*2^n - 12,
y_n = N + 14 - 14*2^n + 2n.
`

The recurrence identities are kernel-checked in `X_succ` and `Y_succ`.

The halting precursor is an even state with `y=4`: one step sends it to odd `a`, `c=2`, and the next high-level call halts. Solving `y_n=4` gives the sparse family

`
N_n = 14*2^n - 2n - 10,      n >= 0.
`

Since a reset has `N=r+1`, the corresponding dangerous zero-reset coordinates are

`
r_n = 14*2^n - 2n - 11
    = 3, 15, 41, 95, 205, 427, 873, 1767, 3557, 7139, ...
`

For these starts, all earlier affine states remain in the direct-branch regime. For `j<n`,

`
y_j-(x_j+10)
 = 14*(2^n-2^(j+1)) - 2*(n-j) + 6 > 0.
`

At the tightest case `j=n-1` this equals 4; moving backward increases it. Therefore `P1(r_n,0)` really does drive the acceleration to the halting gate after `2n+2` successful high-level transitions counting the initial reset.

Conversely, within a positive even episode, if `y>=x+10` the affine rule applies. If `y<=x+8` and `y>=6`, the next odd-a `G` evaluation either takes its boundary branch to an odd second coordinate or first recurses to an odd second coordinate, after which oddness is preserved. The remaining special values are `y=2` (returns to zero) and `y=4` (halts). Hence an episode beginning at `P1(r,0)` can halt before the next zero reset **iff** `r=r_n` for some `n`.

This converts Agent 1's open reachability question for `P1(a,4)` into the more specific question:

> Can the actual blank-tape orbit ever reach a zero-reset state `P1(r_n,0)` with `r_n=14*2^n-2n-11`?

## 3. Computational cross-check and present limit

I simulated 30,000,000 high-level transitions from the certified start `P1(2,1)`. There was no halt and no dangerous reset. Only 17 `c=0` states occurred in that prefix, at reset coordinates

`
4, 10, 58, 81, 278, 634, 5881, 9702, 12113, 28074, 29561,
405562, 2163590, 2453178, 10123514, 11319782, 23880729.
`

None belongs to the exponential family above. This is finite evidence only. It supplies no universal avoidance theorem.

As an additional sanity check, exhaustive direct evaluation of the high-level map for every reset coordinate `0 <= r < 10000` agreed exactly with the criterion above: the halting reset coordinates were
`3,15,41,95,205,427,873,1767,3557,7139`.

## 4. Verification

Using local Lean 4.36.0-rc2:

`lean Burst.lean`

All printed theorem dependencies contain only standard Lean axioms `propext` and `Quot.sound`; no `sorryAx` appears. The file is an arithmetic restatement of the published high-level map, so its link to the original Turing machine relies on DeepMind's already certified bridge.

**Next research target:** derive a return map on the subsequence `c=0` and prove it avoids `r_n`. That would prove this holdout nonhalting.
