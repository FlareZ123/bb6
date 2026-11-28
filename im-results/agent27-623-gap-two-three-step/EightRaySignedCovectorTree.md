# #623 eight-ray gates as a signed covector tree

**Status:** exact algebraic repackaging of the candidate eight-ray source theorem. This is not an all-time root invariant, and the source theorem remains subject to the `eight-ray-full` CI target.

## Coordinates

For a section state (D(u,v)), let
[
m=min(u,v),quad L=max(u,v),quad p=L-m,quad q=m.
]
Use the exact global signed coordinates from [Agent 1's phase-correct bridge](../agent1-623-sync-only/GlobalSignedPQBridge.md):
[
U=6q,qquad V=2p-gamma_s,qquad
P:=V+gamma_s=2p,quad Q:=U=6q,
]
where (gamma_sin{18,10,2,4}) is the source-sector phase. The phase is essential: (P
e V) in general.

For any positive ray coefficients (A_0,B_0),
[
6(A_0L-B_0m)
=3left(A_0P-rac{B_0-A_0}{3}Qight)
]
whenever (3mid(B_0-A_0)). Thus the cone
[
A_0Lle B_0m+C,qquad B_0mle A_0L+D
]
is exactly
[
-2Dle aP-bQle2C,qquad
a=A_0,quad b=(B_0-A_0)/3.
]

## The eight physical strips

The eight rays from [EightRaySource.lean](EightRaySource.lean) become:

| ((a,b)) | Strip (-2Dle aP-bQle2C) |
|---|---|
| (1,40) | (C=214N+23n+1183, D=2N+3n+225) |
| (40,1) | (C=45N+3n+321, D=93N+23n+541) |
| (13,16) | (C=94N+3n+501, D=26N+23n+283) |
| (16,13) | (C=81N+23n+523, D=33N+3n+219) |
| (4,25) | (C=136N+10n+743, D=8N+10n+200) |
| (25,4) | (C=45N+10n+314, D=57N+10n+335) |
| (7,19) | (C=106N+10n+584, D=14N+10n+203) |
| (19,7) | (C=54N+10n+353, D=42N+10n+266) |

Here (N=n+3). The source theorem states that any hypothetical blank-root halt forces some genuine root state into at least one of these eight strips for some (nge13).

The four coupled predecessor rays are the seed covectors
[
(1,13), (13,1), (4,7), (7,4).
]
One ordinary predecessor step generates exactly two covectors from each seed:
[
(a,b)longmapsto(a,a+3b)quad(L),qquad
(a,b)longmapsto(a+3b,a)quad(R).
]
This gives the eight pairs above.

## Exact cocycle transport

The global signed bridge gives, with (T_s=delta_s-eta_s),
[
L:quad P'=P-Q-2T_s,quad Q'=3Q+6delta_s,
]
[
R:quad P'=Q-P+2T_s,quad Q'=3P+6eta_s.
]
Therefore the covector (F_{a,b}=aP-bQ) obeys the exact affine identities
[
F_{a,b}(P',Q')
=F_{a,a+3b}(P,Q)-2aT_s-6bdelta_s
quad(L),
]
[
F_{a,b}(P',Q')
=-F_{a+3b,a}(P,Q)+2aT_s-6beta_s
quad(R).
]
The inverse-ray tree is thus the transpose action of the two source matrices, with the exact drain-statistic corrections exposed rather than hidden in an (O(n)) estimate.

## Research target and limitation

The next useful theorem is not another finite root scan. It is a root-history estimate for the eight affine covectors, strong enough to show that every authentic blank-root state stays outside all eight (O(n))-width strips, or else to identify an actual hit. The exact global coordinates above do **not** by themselves close the moving S-window: the low-boundary quotient carry, sector phase, and dynamic cut shift from [WindowQuotientInterface.md](../agent1-623-sync-only/WindowQuotientInterface.md) must remain in any induction.

No BB(6) bound, #623 nonhalting decision, or all-time avoidance result is claimed here.
