# #623 eight-ray gates as a signed covector tree

**Status:** exact algebraic repackaging of the candidate eight-ray source theorem. This is not an all-time root invariant, and the source theorem remains subject to the \`eight-ray-full\` CI target.

## Coordinates

For a section state \`D(u,v)\`, let

\`\`\`
m = min(u,v),  L = max(u,v),  p = L-m,  q = m.
\`\`\`

Use the exact global signed coordinates from [Agent 1's phase-correct bridge](../agent1-623-sync-only/GlobalSignedPQBridge.md):

\`\`\`
U = 6q,  V = 2p - gamma_s,
P := V + gamma_s = 2p,  Q := U = 6q,
\`\`\`

where \`gamma_s\` is the source-sector phase in \`{18,10,2,4}\`. The phase is essential: \`P != V\` in general.

For any positive ray coefficients \`A0,B0\` with \`3 | (B0-A0)\`,

\`\`\`
6*(A0*L - B0*m)
  = 3*(A0*P - ((B0-A0)/3)*Q).
\`\`\`

Thus the cone

\`\`\`
A0*L <= B0*m + C
B0*m <= A0*L + D
\`\`\`

is exactly the signed-coordinate strip

\`\`\`
-2*D <= a*P - b*Q <= 2*C,
a = A0,  b = (B0-A0)/3.
\`\`\`

## The eight physical strips

The eight rays from [EightRaySource.lean](EightRaySource.lean) become:

| (a,b) | Strip constants: -2D <= aP-bQ <= 2C |
|---|---|
| (1,40) | C=214N+23n+1183, D=2N+3n+225 |
| (40,1) | C=45N+3n+321, D=93N+23n+541 |
| (13,16) | C=94N+3n+501, D=26N+23n+283 |
| (16,13) | C=81N+23n+523, D=33N+3n+219 |
| (4,25) | C=136N+10n+743, D=8N+10n+200 |
| (25,4) | C=45N+10n+314, D=57N+10n+335 |
| (7,19) | C=106N+10n+584, D=14N+10n+203 |
| (19,7) | C=54N+10n+353, D=42N+10n+266 |

Here \`N=n+3\`.

The physical halt theorem is being strengthened to retain the transported scale interval

\`\`\`
n >= 13
3^(n-4) <= m
m+3 < 3^(n+3)
\`\`\`

at the same genuine root state. This is essential: without the lower scale relation, an avoidance premise quantified over every \`n>=13\` is vacuous because the strip widths grow linearly with \`n\`. The updated statement is pending end-to-end source CI.

The lower bound follows from the two preceding successful source steps. If \`m_p\` is the terminal-strip predecessor minimum, \`m_q\` the next predecessor minimum, and \`m_r\` the fifth-predecessor minimum, then

\`\`\`
3^(n-1)-3 <= m_p <= p_y <= 3*m_q + 4N + 20
m_q <= q_y <= 3*m_r + 4N + 20
\`\`\`

and hence

\`\`\`
3^(n-1) <= 9*m_r + 16N + 83.
\`\`\`

For n>=13, \`18*3^(n-4) >= 16N+83\`; combining with \`3^(n-1)=27*3^(n-4)\` gives \`3^(n-4)<=m_r\`. The upper scale bound \`m_r+3<3^(n+3)\` is already transported by the strict-mass and terminal upper-scale estimates.

## The inverse covector tree

The four coupled predecessor rays are the seed covectors

\`\`\`
(1,13), (13,1), (4,7), (7,4).
\`\`\`

One ordinary predecessor step generates exactly two covectors from each seed:

\`\`\`
(a,b) -> (a,a+3b)   [left]
(a,b) -> (a+3b,a)   [right]
\`\`\`

This gives the eight pairs above.

## Exact cocycle transport

The global signed bridge gives, with \`T_s=delta_s-beta_s\`,

\`\`\`
left:  P' = P-Q-2*T_s,  Q' = 3*Q+6*delta_s
right: P' = Q-P+2*T_s,  Q' = 3*P+6*beta_s.
\`\`\`

Therefore the covector \`F_(a,b)=aP-bQ\` obeys the exact affine identities

\`\`\`
left:
  F_(a,b)(P',Q') = F_(a,a+3b)(P,Q) - 2*a*T_s - 6*b*delta_s

right:
  F_(a,b)(P',Q') = -F_(a+3b,a)(P,Q) + 2*a*T_s - 6*b*beta_s.
\`\`\`

The inverse-ray tree is thus the transpose action of the two source matrices, with the exact drain-statistic corrections exposed rather than hidden in an O(n) estimate.

## Research target and limitation

The next useful theorem is not another finite root scan. It is a root-history estimate for the eight affine covectors, strong enough to show that every authentic blank-root state stays outside all eight scale-corrected O(n)-width strips, or else to identify an actual hit. The exact global coordinates above do **not** by themselves close the moving S-window: the low-boundary quotient carry, sector phase, and dynamic cut shift from [WindowQuotientInterface.md](../agent1-623-sync-only/WindowQuotientInterface.md) must remain in any induction.

No BB(6) bound, #623 nonhalting decision, or all-time avoidance result is claimed here.
