# Forced predecessor tail for the U5 second-cone seen cell

**Status:** exact source reduction, **not** a reachability exclusion. The earlier version of this note incorrectly claimed that its terminal k=0 state had no predecessor. Agent 48's existing source-certified zero-middle-counter theorem shows that the terminal has precisely the allowed (a\equiv1\pmod4) shape. The correction below supersedes the earlier claim.

## Exceptional Side preimage

In the proposed second backward cone for the q=1 parent at (t=128n+35, n\equiv2\pmod4), a Side target has
[
a\equiv5\pmod{32},\quad c\equiv a+30\pmod{64},\quad c\ge a,\quad c\ge4.
]
The exceptional source is ((a+2,(c-1)/2,0)). Split (a\pmod{64}):

- If (a\equiv5\pmod{64}), the source projects to the M32-absent cells ((7,17,0)) or ((39,17,0)).
- If (a\equiv37\pmod{64}), write
  [
  a=37+64u,\qquad c=67+64v.
  ]
  The inequality (c\ge a) gives (v\ge u), and the exceptional source is
  [
  (39+64u, 33+32v, 0).
  ]
  Its M32 representative ((39,33,0)) is seen, so the M32-only forbidden-cell argument cannot close this branch.

## Forced predecessor chain and its actual endpoint

The exact CLine clauses force the following predecessors:
[
egin{aligned}
(39+64u,33+32v,0)
&\leftarrow(39+64u,32+32v,1)\
&\leftarrow(39+64u,30+32v,3)\
&\leftarrow(40+64u,29+32v,4).
end{aligned}
]

For states ((A,K,C)) with (C\ge4), (A\ge40), and (K\ge3), the only possible immediate predecessor is ((A+1,K-1,C+1)): the (c=0) clauses can produce target middle counters only (0,1,2), the (c=1,3) clauses target (c=0,1), (c=2) has no edge, and the (c\ge4,a=0) clauses produce middle counter (0) or (2). Iterating this forced predecessor (29+32v) times reaches
[
(69+64u+32v, 0, 33+32v).
]

This is **not** a predecessor-free terminal. Put
[
K=16+16u+8v,\qquad D=29+32v.
]
Then
[
69+64u+32v=4K+5,qquad 33+32v=D+4,
]
and the exact CLine zero-left clause has the predecessor
[
(0,2K+1,D+4)=(0,33+32u+16v,33+32v).
]
Indeed, (2K+1) is odd and its output left counter is (4\lfloor(2K+1)/2\rfloor+5=4K+5).

## Relation to the existing zero-middle theorem

Agent 48 already proved, against the exact original CLine source, that every reachable ((a,0,c)) satisfies (a\equiv1\pmod4), and more precisely belongs to
[
(5,0,1),\quad (1,0,2k+2),\quad (4k+5,0,d+4).
]
See `im-results/agent48-c-middle-zero/KZeroMod4.lean`, theorem `BB6.Agent48.reached_middle_zero_shape`. The forced-tail endpoint is exactly in the third allowed shape. The earlier claim in this note that reachable k=0 states must have (a=1) or (a\equiv3\pmod4) was wrong and is withdrawn.

Therefore this chain only reduces the seen M32 Side lift to the zero-left state
[
(0, 33+32u+16v, 33+32v).
]
It does **not** exclude that state. The next useful step is to apply the existing exact zero-left predecessor calculus (for example Agent 21's `CBack.reached_zero_prev`, `reached_zero_hub`, and related lemmas) to this family, or derive a new source invariant for it.

## Scope

This is a useful reduction of the exceptional (a\equiv37\pmod{64}) Side branch, but it does not complete the second cone, the q=2 parent family, or the full (w\equiv101\pmod{128}) class. No Lean compilation is claimed for this note.
