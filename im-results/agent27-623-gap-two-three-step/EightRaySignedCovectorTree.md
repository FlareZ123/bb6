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

The physical halt theorem now retains the transported scale interval

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


## Direct S-window scalar forms

For the signed window coordinates used by the boundary transducer, set

\`\`\`
x = 2*(p-3q) - gamma_s
y = 6*q.
\`\`\`

Then \`P=x+y+gamma_s\` and \`Q=y\`. For an original ray pair \`(A0,B0)\),

\`\`\`
6*(A0*L-B0*m)
  = 3*A0*x + (4*A0-B0)*y + 3*A0*gamma_s.
\`\`\`

Thus the eight forms to feed to a signed scalar-carry transducer have coefficient pairs \`(A,B)=(3*A0,4*A0-B0)\`:

| Ray (A0,B0) | Scalar form \`A*x+B*y+c\` |
|---|---|
| (1,121) | \`3*x - 117*y + 3*gamma_s\` |
| (40,43) | \`120*x + 117*y + 120*gamma_s\` |
| (13,61) | \`39*x - 9*y + 39*gamma_s\` |
| (16,55) | \`48*x + 9*y + 48*gamma_s\` |
| (4,79) | \`12*x - 63*y + 12*gamma_s\` |
| (25,37) | \`75*x + 63*y + 75*gamma_s\` |
| (7,64) | \`21*x - 36*y + 21*gamma_s\` |
| (19,40) | \`57*x + 36*y + 57*gamma_s\` |

The strip bounds are \`-6*D <= A*x+B*y+c <= 6*C\`, with the matching \`C,D\` from the previous table. A low-digit scalar transducer can use Euclidean division:

\`\`\`
c_(i+1) = floor((A*x_i + B*y_i + c_i)/3)
digit_i = (A*x_i + B*y_i + c_i) mod 3.
\`\`\`

The coefficients are bounded (\`|A|<=120\`, \`|B|<=117\`) and the phase constant is \`3*A0*gamma_s\`. The remaining issue is not the algebraic identity: it is to retain the actual low-boundary carry at the moving S-window cut and prove that the authentic root word forces a sufficiently high nonmonochromatic output digit. A truncated window must not silently reset this carry.


## Uniform strip-width target for the S-window proof

Across all eight rows, after substituting N=n+3, the largest upper-side error is

\`\`\`
C_max(n) = 237*n + 1825,
\`\`\`

and the largest lower-side error is

\`\`\`
D_max(n) = 116*n + 820.
\`\`\`

Therefore every eight-ray cone is excluded as soon as its corresponding scalar form F satisfies

\`\`\`
abs(F) > W(n),   W(n) = 1422*n + 10950.
\`\`\`

Using the transported scale relation n<=ell+3 (where ell is the authentic S-mass window depth), it suffices to prove

\`\`\`
abs(F) > 1422*ell + 15216.
\`\`\`

A transducer proof that finds a nonzero ternary output digit at position k, while bounding the actual low-boundary scalar carry by H, would give a sufficient inequality of the form

\`\`\`
3^k - H > 1422*ell + 15216.
\`\`\`

This isolates the quantitative target for the moving-window argument. The coefficient ranges alone do not prove the needed carry bound or the required high nonzero digit; those remain the genuine open steps.


## Uniform scalar-carry magnitude bound

For all eight scalar forms, \`|A|+|B|<=237\`. Also \`c_0=3*A0*gamma_s\` has \`|c_0|<=2160\`, since \`A0<=40\` and \`gamma_s<=18\`. Every ternary input digit \`x_i,y_i\` lies in \`{0,1,2}\`, so

\`\`\`
|A*x_i+B*y_i| <= 2*(|A|+|B|) <= 474.
\`\`\`

For the exact Euclidean carry recurrence

\`\`\`
c_(i+1) = floor((A*x_i+B*y_i+c_i)/3),
\`\`\`

the magnitude envelope obeys

\`\`\`
H_(i+1) = ceil((474+H_i)/3),   H_0=2160,
H_1=878, H_2=451, H_3=309, H_4=261, H_5=245, H_6=240.
\`\`\`

Thus after six low ternary digits, the scalar carry magnitude is at most 240, uniformly over the eight rays, all four sector phases, and arbitrary input digits. In particular, \`240<3^5\`.

This coefficient-only bound does **not** by itself imply that a nonzero high quotient forces a large absolute scalar form: for a negative Euclidean quotient, a low residue near \`3^k-1\` can partially cancel it. A complete exclusion still needs the signed-complement argument showing that the authentic nonmonochromatic middle output prevents the long all-2 (negative) or all-0 (positive) low-residue pattern required for a small absolute value.


## Signed-complement criterion for a small absolute form

Let the first k Euclidean ternary digits of an integer scalar form F be represented by

\`\`\`
F = 3^k*q + r,   0 <= r < 3^k.
\`\`\`

If \`abs(F)<=W<3^k\`, then \`q\` must be either 0 or -1. Indeed, q>=1 gives F>=3^k>W, while q<=-2 gives F<=-3^k-1.

- If q=0, then r=F<=W. Every ternary digit d_j of r with \`3^j>W\` must therefore be 0.
- If q=-1, then \`r2=3^k-1-r=-F-1\` lies in \`[0,W-1]\`. The ternary digits of r2 are \`2-d_j\`, so every digit d_j with \`3^j>W\` must be 2.

Consequently, a nonmonochromatic block of output digits entirely at positions j satisfying \`3^j>W\` rules out \`abs(F)<=W\`. This argument does not require a separate magnitude bound on q: a small signed integer forces the high digits of its low residue to be uniformly 0 or uniformly 2 according to the sign.

For the eight strips, \`W=1422*ell+15216\`. The exact remaining transducer task is therefore to locate a nonmonochromatic output block J within the first k digits, with \`3^min(J)>1422*ell+15216\`, while preserving the true carry at the moving S-window cut. The carry magnitude bound above is secondary; the signed-complement criterion is stronger.


## Existing reset machinery to reuse

The relevant finite carry artifacts already exist:

- [PostResetCarryPairTransducer.json](../agent48-623-tight-window/PostResetCarryPairTransducer.json) is a 66-state paired L/R carry transducer; each of the nine raw digit-pair inputs records both branch output pairs and the next paired state.
- [SourceCarryResetProduct.json](../agent24-machine623-shifted-reset-product/SourceCarryResetProduct.json) is the reachable source-to-target carry/reset product with one- and two-symbol output skips.
- [ExactSeedCarry84.json](../agent24-machine623-shifted-reset-product/ExactSeedCarry84.json) records exact source-derived seeds for the 84 correction-only S-window suffix exceptions.

The existing shift-aware reset overlap certificate establishes a nonmonochromatic x-output suffix for its checked reset language and carry rectangles. That x-only property does not automatically transfer to the eight forms A*x+B*y+c. The next finite product should either prove nonmonochromaticity separately for each coefficient pair over the exact source-derived seed set, or prove a symbolic condition on the paired output word that implies nonmonochromaticity for all eight forms. Keep the branch-dependent one-symbol trim and exact low-cut carry in the product; a generic reset label without the source phase is insufficient.
