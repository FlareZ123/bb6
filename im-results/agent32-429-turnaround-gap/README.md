# #429 high-level return gap coordinate

**Status:** exact algebraic reduction of the published high-level map; not a proof that #429 halts or does not halt. Keep this in `im-results/`.

## Source and root

The external DeepMind Cryptids Lean module defining `highLevelNext` on `J(u,w)` is [here](https://github.com/google-deepmind/cryptids/blob/main/BusyBeaver/BB6/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean). The repository's [raw-parent dossier](../agent32-429-raw-parent/README.md) records the exact blank-root entry to `J(0,0)` after 35 original-machine steps.

Write a high-level state as `J(u,w)`, with (u,w\in\mathbb N), and put
[
g(u,w)=2u-w+3.
]
This is the signed gap to the outer-ladder boundary.

## Outer-ladder closure in closed form

The outer branch of `highLevelNext` is selected exactly when
[
w\ge 2u+3\quad\Longleftrightarrow\quad g\le0,
]
and applies
[
(u,w)\longmapsto(2u+3,\;w-2u-3).
]
One outer step therefore changes the gap by
[
g' = 2(2u+3)-(w-2u-3)+3 = g+4u+9.
]

After (n) consecutive outer steps, direct induction gives
[
\begin{aligned}
u_n&=2^n(u+3)-3,\\
w_n&=w-2(u+3)(2^n-1)+3n,\\
g_n&=g+4(u+3)(2^n-1)-3n.
\end{aligned}
]
Thus the outer ladder is not an opaque simulation: from any post-boundary state, its exact closure is the least (n\ge0) for which (g_n\ge1). The gap is strictly increased at each outer step because (4u_n+9>0).

## Halting is the fixed target (g=4)

For odd (w=2m+1), let (d=u-\lfloor w/2\rfloor=u-m). Then
[
g=2u-(2m+1)+3=2d+2.
]
For even (w), instead (g=2d+3), which is odd. Consequently,
[
\boxed{\ g=4\quad\Longleftrightarrow\quad w\text{ odd and }d=1\ }.
]
This is exactly the `none`/halting branch of `highLevelNext`. Hence #429's unresolved question in this representation is whether the boundary-return orbit ever hits the single scalar target (g=4). The initial state `J(0,0)` has (g=3), so it is not itself a halt.

## Boundary transition table in gap coordinates

The following are the non-outer branches of `highLevelNext`. Here (d=u-\lfloor w/2\rfloor).

| Boundary condition | Old gap (g) | New state ((u',w')) | New gap (g') |
|---|---:|---|---:|
| (w=2u+2) | (1) | ((0,4u+18)) | (-4u-15) |
| (w=2u+1) | (2) | ((11,4u+2)) | (23-4u) |
| (w=2u) | (3) | ((0,4u+12)) | (-4u-9) |
| (w) even, (d=1) | (5) | ((0,2w+12)) | (-4u-5) |
| (w) even, (d\ge2) even | (2d+3) | ((11,2u+w-2)) | (g+24-4u) |
| (w) even, (d\ge3) odd | (2d+3) | ((0,2u+w+10)) | (g-4u-10) |
| (w) odd, (d=1) | **(4)** | halt | — |
| (w) odd, (d=2) | (6) | ((0,2w+8)) | (1-4u) |
| (w=1), (d\ge4) even | (2u+2) | ((11,2u+10)) | (15-2u) |
| (w\ge3) odd, (d\ge4) even | (2d+2) | ((d+7,2w-4)) | (3g+13-4u) |
| (w) odd, (d\ge3) odd | (2d+2) | ((d+3,2w)) | (3g+1-4u) |

All entries follow by substituting the corresponding branch formula into (g'=2u'-w'+3). The table plus the closed-form outer closure gives a complete gap-coordinate presentation of the high-level return process.

## What this does and does not establish

- It replaces the halt test (w=2u-1) by the fixed target (g=4).
- It gives an exact, non-iterative formula for every maximal outer-ladder segment.
- It exposes the remaining mathematical task: analyze the successive boundary resets and prove or refute a future return to (g=4).
- It does **not** establish an all-time invariant, a first hitting time, or a halt/nonhalt decision. The published (sim10^{110}) expectation remains heuristic.
- The next useful direction is to derive a return recurrence or congruence invariant for the boundary gap, potentially combining this coordinate with the existing 58-class / 2^18 terminal-residue sieve. Further finite-prefix extension alone does not answer the hitting question.
