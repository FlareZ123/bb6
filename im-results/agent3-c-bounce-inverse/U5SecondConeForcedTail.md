# Exact forced-predecessor tail for the U5 second-cone seen cell

**Status:** source-transition derivation; not yet Lean-compiled. It repairs the specific M32 obstruction at the exceptional cell ((39,33,0)) by using the exact CLine predecessor relation rather than a stronger quotient.

## Exceptional Side preimage

In the proposed second backward cone for the q=1 parent at (t=128n+35, n\equiv2\pmod4), a Side target has
[
a\equiv5\pmod{32},\quad c\equiv a+30\pmod{64},\quad c\ge a,\quad c\ge4.
]
The exceptional source is ((a+2,(c-1)/2,0)). Split (a\pmod{64}):

- If (a\equiv5\pmod{64}), the source projects to the M32-absent cells ((7,17,0)) or ((39,17,0)).
- If (a\equiv37\pmod{64}), write
  [
  a=37+64u,qquad c=67+64v.
  ]
  The inequality (c\ge a) gives (v\ge u), and the exceptional source is exactly
  [
  (39+64u, 33+32v, 0).
  ]
  Its M32 representative ((39,33,0)) is seen, so the earlier M32-only forbidden-cell argument cannot close this branch.

## Exact original-source predecessor chain

The exact CLine clauses imply the following forced predecessors:

[
egin{aligned}
(39+64u,33+32v,0)
&\leftarrow(39+64u,32+32v,1)\
&\leftarrow(39+64u,30+32v,3)\
&\leftarrow(40+64u,29+32v,4).
end{aligned}
]

For states ((A,K,C)) with (C\ge4), (A\ge40), and (K\ge3), the only possible immediate predecessor is ((A+1,K-1,C+1)): the (c=0) clauses can produce target right counters only (0,1,2), the (c=1,3) clauses target (c=0,1), (c=2) has no edge, and the (c\ge4,a=0) clauses produce right counter (0) or (2). The (c\ge4,a\ge1) clause is therefore forced.

Iterating this predecessor exactly (29+32v) times reaches
[
(69+64u+32v, 0, 33+32v).
]

This terminal state has no immediate predecessor in the exact CLine map:
- the (c=0,a=0) clause can produce right counter (0) only with left counter (1);
- the (c=0,a=1) special clause produces ((5,0,1));
- the other (c=0) clauses produce right counter (1) or (2);
- the (c=1,2,3) clauses cannot target (c\ge4);
- the (c\ge4,a\ge1) clause has positive target right counter;
- the only (c\ge4,a=0) clause producing right counter (0) has target left counter (2k+5\equiv3\pmod4), whereas (69+64u+32v\equiv1\pmod4).

Every noninitial state in `BB6CLine.Reach` has an immediate predecessor. Hence the terminal state is not reachable, and backward induction excludes the entire exceptional family
[
(39+64u,33+32v,0)qquad(v\ge u).
]

## Scope

This closes the *seen M32 lift* in the (a\equiv37\pmod{64}) part of the second cone's Side-predecessor analysis, without extending the quotient. It does not by itself complete the second cone: the (a\equiv5\pmod{64}) part still needs its M32-absent-cell argument, and the q=2 parent family remains a separate issue. The predecessor chain should be formalized as a Lean lemma against the exact `CLine` definition before it is treated as a theorem.


## General source-image corollary

The terminal check is an instance of a simpler global necessary condition. From the exact CLine transition clauses, any state ((a,0,c)) with (c\ge4) can have an immediate predecessor only in one of two cases:

1. the (c=0,a=0) source clause, which forces (a=1); or
2. the (c\ge4,a=0,k\) odd source clause, which forces (a=2k+5\equiv3\pmod4).

All other source clauses either produce positive target right counter or target (c<4). Since the blank initial state has (c=1), every reachable state with right counter zero and (c\ge4) must satisfy

[
a=1\quad\text{or}\quad a\equiv3\pmod4.
]

In particular, every ((a,0,c)) with (c\ge4, a\ge5, a\equiv1\pmod4) is source-unreachable. This single source-image lemma excludes the entire forced-tail endpoint ((69+64u+32v,0,33+32v)), without checking its individual predecessor cases. It is a reusable global constraint, not specific to U5.
