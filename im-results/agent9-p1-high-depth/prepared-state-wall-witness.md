# Prepared-state wall witness at n = 808

**Status: intermediate computational construction, not a root-reachability result.**

## Result

The branch-A high-depth restart conditions admit a source-legal continuation to the shifted wall after the first shallow edge and three further low edges of depths **0, 1, 2**. The construction has:

- (n=808), (P=2^{808});
- last high-depth edge (t=5);
- (s=(n+2)/3=270) depth-two edges before the first shallow edge;
- first shallow edge of depth (0);
- three subsequent edges of depths (0,1,2);
- 275 source transitions and total inverse-cost increment 823 from the prepared parent to the wall.

Every local source inverse guard and exact integer division in this finite segment was checked with exact integer arithmetic. The reproducible checker is `prepared_state_wall_witness.mjs`.

**This is not a path from the original blank-root state.** The state immediately before the (t=5) edge is checked against the mass invariant and the local source-edge conditions, but its membership in the original `OddCone`/`CountCone` is not established. Thus this does not prove P1 halts and does not contradict a theorem whose hypothesis includes original-root reachability.

It does rule out a stronger proposed strategy: one cannot exclude every wall-reaching low suffix from *arbitrary locally legal prepared high-depth restart states* using only the restart scalar/coordinate conditions. A successful P1 exclusion must exploit an invariant inherited from the original root, or prove that this particular prepared parent is unreachable.

## Exact arithmetic

The terminal equation for the three post-first-shallow depths ((0,1,2)) is
[
34P=2116u+1272.
]
For (n=808), this gives
[
u=\frac{34\cdot 2^{808}-1272}{2116}
 =\frac{17\cdot 2^{807}-318}{529}\in\mathbb N,
]
because
[
17\cdot 2^{807}\equiv318\pmod{529}.
]

The branch-A restart defect relation is
[
49D=18P-196u+14n+48,
\qquad M=14u-n-3.
]
Here (D) is a positive even integer. In particular, (2^{808}\equiv44\pmod{98}), so
[
18P+14n+48\equiv18\cdot44+14\cdot808+48
=12152\equiv0\pmod{98};
]
the term (196u) is also divisible by 98.

Put
[
m_0=M-n,\quad m_p=m_0-6,\quad X=32D,
]
[
q=14P-X-2m_p-2n-10,
\quad b_p=2q,\quad d_p=X-q-3,
]
[
c_p=D-3,\quad k_p=\frac{q+X-c_p-15}{2}.
]
The prepared parent ((b_p,d_p,m_p)) satisfies the mass invariant and the local (t=5) source equations; its child is
[
(b_0,d_0,m_0)=(2k_p-4,c_p+4,m_0).
]

After 270 depth-two edges, the path reaches the first-shallow parent
[
(b_s,d_s,m_s)=(12P-24u-12,;2P-4u+1,;M+2).
]
Its depth-zero child is
[
(b_1,d_1,m_1)=(6P-12u-12,;8P-16u-1,;M+3).
]
Three further source edges of depths (0,1,2) reach a state satisfying
[
b_f+4m_f+4n+20=12P,
]
the shifted wall equation.

For a source edge of depth (t\in\{0,1,2,5\}), the checker uses
[
c=\frac{d+b/2+3}{2^t}-3,
\qquad
k=\frac{b+d-c-2t-2}{2},
\qquad
(b',d',m')=(2k-4,c+4,m+t+1),
]
and checks (b\ge8), (4\mid b), (d) odd, exact divisibility, (c) odd, and (k\ge2).

## Research consequence

The 27 terminal equations for termination by the third edge remain useful, but a blanket extension to arbitrary prepared restart states is false: the fourth-edge sequence ((0,1,2)) is locally realizable. The next decisive question is whether the prepared parent ((b_p,d_p,m_p)) can belong to the original root cone. Research should now target root-cone reachability or a stronger root-inherited invariant, not another generic local-suffix exclusion.
