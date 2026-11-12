# High-depth restart potential after shallow/deep transitions

**Status:** derived algebraic identities; no new BB(6) or unrestricted-wall theorem is claimed.

This note records a useful state potential for connecting the depth-0/1/2 source-word work to the unrestricted `CountCone` frontier. It also records why the depth-two energy recurrence cannot simply be generalized by replacing powers of 8 with arbitrary powers of 2.

## Coordinates

Write the source state as `(b,d,m)`, put `P=2^n`, and assume
`b+d+2m+2n+13=14P`.
Use
`W=b+4m+4n+20`, `B=m+n+6`, and `F=W-12P-2B`.
Then `b=W-4B+4`, `d=14P-W+2B-5`, and `F+2B=W-12P`.
At the exact shifted wall `W=12P`, one has `F=-2B<0`.

Under the global mid-cost cap `2m+n+2<=5P`,
`B<=(5P+n+10)/2 = 2.5P+n/2+5`.

## Exact one-step recurrence

For an inverse edge of depth `t`, the exact inverse equations give
`2^t(c+3)=d+b/2+3` and `2k+c+2t+2=b+d`.
The next state is `b'=2k-4`, `d'=c+4`, `m'=m+t+1`, so `B'=B+t+1`.
Eliminating `b,d,k,c` using the mass identity yields

`2^(t+1) * (F' + 6) = F + 2B + (2^(t+2)-16)P`.

Equivalently,
`F' = (2 - 8/2^t)P - 6 + (F+2B)/2^(t+1)`.

Special cases:
- depth 0: `2(F'+6)=F+2B-12P`;
- depth 1: `4(F'+6)=F+2B-8P`;
- depth 2: `8(F'+6)=F+2B`;
- depth at least 3: `F'=(2-8/2^t)P-6+(F+2B)/2^(t+1)`.

## Sign consequences under the cost cap

Since `d>=1`, mass gives
`F+2B=W-12P=2P+2B-d-5 <= 2P+2B-6`.

For t=0,
`2(F'+6) <= 2B-10P-6 <= -5P+n+4 < 0`
for n>=14. For t=1,
`4(F'+6) <= 2B-6P-6 <= -P+n+4`.
Thus every shallow edge (depth 0 or 1) sends `F'` strictly negative under the global cost cap.

On the other hand, `W>=0` gives `F+2B=W-12P>=-12P`. For t>=3,
`F' >= (2-14/2^t)P-6 >= P/4-6 > 0`
for n>=14. So every depth-at-least-three edge resets the defect to a positive value bounded below by `P/4-6`.

A depth-two edge obeys `F'=(F+2B)/8-6`. If it follows a depth-at-least-three edge, then `F>=P/4-6` and `B>=n+6>=20`, hence
`F' >= P/32-7/4 > 0`.
Therefore, after a depth-at-least-three edge, any subsequent sequence consisting only of depth-two edges keeps F positive. Since the wall has F<0, a path reaching the wall after any depth-at-least-three edge must contain a later shallow edge.

This is a precise sign-dynamics statement: depth >=3 resets F positive; depth 2 preserves that positive region; depth 0/1 resets F negative. It is a useful decomposition principle, but it does **not** yet bound how many shallow edges are needed after the last high-depth reset.

## Why the depth-two energy does not extend by a naive exponent substitution

The depth-two model uses
`I(P,W,B)=49W-588P-112B+384=49F-14B+384`.
For t=2, the recurrence gives `I_before=8*I_after`, exactly the `TwoRun.run_energy` theorem.

For general t, direct substitution instead gives
`I_before - 2^(t+1)*I_after
 = 4*(2^t*(-49P+7B+7t-38)+196P-28B+96)`.
This correction vanishes at t=2, but not uniformly for t>=3. Therefore a run of arbitrary depths cannot be represented merely by replacing `8^u` with `2^e` in the current five-shallow recurrence. Any unrestricted extension needs a different affine/vector recurrence or a separate defect argument.

## Concrete next lemma

A useful next target is a quantitative shallow-suffix theorem starting from a state produced by a depth>=3 edge. Such a state has `F>=P/4-6`, and the global cost cap bounds B. One would need to show that a sequence of at most five depth-0/1 resets, interspersed with depth-two steps, cannot reach `F=-2B`. The existing `source_low_trace_wall_needs_six_shallows` theorem proves this only from the original root; it does not yet cover this arbitrary post-high-depth starting state.

This is the precise gap between the current depth-2 source theorem and the unrestricted `CountCone` case.
