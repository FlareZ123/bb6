# Mod-128 reverse-parent obstruction for two P1 restart families

**Status:** exact finite-state arithmetic exclusion; computationally reproducible, not Lean-formalized. This is an intermediate result and does not decide P1 or BB(6).

## Scope

The P1 fourth-edge local-survivor analysis leaves two parameter families with restart states

\[
\begin{aligned}
\mathrm{I}:&\quad n=5362+595056h,\qquad
u=(17\cdot2^n-636)/1058,\\
\mathrm{II}:&\quad n=9538+703248h,\qquad
u=(87\cdot2^n-712)/1198.
\end{aligned}
\]

The associated restart state is represented in the \((D,N,m)\) coordinates by

\[
D_R=\frac{18P-196u+14n+48}{49},\qquad
N_R=14P-28u+2n-1,\qquad
m_R=14u-2n-3,
\]
where \(P=2^n\). These are the states used in the 249/343 uniform-shadow analysis; see [Agent 9's shadow dossier](../agent9-p1-shadow/Uniform343Shadow.md) and [the fourth-edge survivor reduction](../agent50-p1-dyadic-width/fourth_edge_terminal_survivors.md).

The result below excludes root ancestry for **\(h\equiv0,3\pmod4\)** in both families. It does not exclude the complementary classes \(h\equiv1,2\pmod4\), and it does not classify other P1 inverse exits.

## Exact reverse-parent map and invariant

For a reverse-parent step of positive cost \(k=t+1\), the exact coordinate map is

\[
N'=N+2k,\qquad D'=2^kD-N'-1,\qquad m'=m-k.
\]

Consequently,

\[
N'+2m'=N+2m.
\]

At the root \((b_0,d_0)=(14P-2n-16,3)\), the coordinates are

\[
(D_0,N_0,m_0)=(2,\ 14P-2n-7,\ 0).
\]

At either restart state, direct substitution gives the same conserved quantity

\[
N_R+2m_R=N_0=14P-2n-7.
\]

Thus along any genuine reverse-parent chain from a restart state to the root, \(N=N_0-2m\). Reducing one parent step modulo 128 gives

\[
\boxed{\quad
m'\equiv m-k,\qquad
D'\equiv 2^kD-N_0+2m'-1\pmod{128}.
\quad}
\]

## Finite over-approximation

The graph uses vertices \((D,m)\in(\mathbb Z/128\mathbb Z)^2\). It deliberately ignores the source interval inequalities, \(k\le m\), and every other legality restriction. It permits **every** integer \(k\ge1\).

All possible costs are represented by only 134 edge labels:

- \(k=1,\ldots,6\), retained exactly;
- \(k=7,\ldots,134\), which represent every residue of \(k\bmod128\) among \(k\ge7\). For all such costs, \(2^kD\equiv0\pmod{128}\).

For each representative \(k\), the graph has the edge

\[
(D,m)\longrightarrow
\left(2^kD-N_0+2(m-k)-1,\ m-k\right)\pmod{128}.
\]

Every actual reverse-parent step is therefore an edge of this larger finite graph. If the root vertex \((2,0)\) is not reachable in this graph, it cannot be reached by a genuine source-parent chain.

## Why odd-prime reductions cannot improve this particular relaxation

For any odd prime `p`, let `r=ord_p(2)`. Since `r\mid p-1`, we have `gcd(r,p)=1`. In the same all-positive-cost relaxation over `F_p^2` (with fixed `N_0`), every vertex reaches every other vertex in at most two edges.

Indeed, by the Chinese remainder theorem, for any current second coordinate `m` and desired next coordinate `m'`, there is a positive `k` satisfying
`k\equiv m-m'\pmod p` and `k\equiv0\pmod r`.
Then `2^k\equiv1\pmod p`, so the edge is
`(D,m)\longrightarrow(D-N_0+2m'-1,m')`.
Given any source `(D,m)` and target `(E,n)`, choose the intermediate coordinate
`m_1\equiv (E-D)/2+N_0-n+1\pmod p`.
Two such identity-multiplier edges then land exactly at `(E,n)`.

This is a no-go theorem for this **specific relaxation**, not for the original source relation: trying another odd-prime modulus while still allowing every positive `k` and dropping source legality cannot exclude the root. The nontrivial mod-128 obstruction comes from the noninvertible 2-adic multiplier and its collapse for `k\ge7`. A stronger sieve must retain source interval/legality conditions or exploit higher 2-adic information.

## Why the start residues depend only on \(h\bmod4\)

Write \(b=2b_{\rm odd}\). The two families have

\[
(b_{\rm odd},\Delta n)=
(529,595056),\qquad(599,703248).
\]

The exact multiplicative orders are

\[
\operatorname{ord}_{529}(2)=253,\quad
\operatorname{ord}_{599}(2)=299,\quad
\operatorname{ord}_{49}(2)=21.
\]

Indeed, \(253=11\cdot23\), \(299=13\cdot23\), and the proper-prime-divisor checks are included in the executable verifier. The progressions satisfy

\[
595056=112\,\operatorname{lcm}(253,21),\qquad
703248=112\,\operatorname{lcm}(299,21).
\]

Since \(n\ge8\), the factor \(2^n\) supplies the full \(2^8\) part of \(b\cdot49\cdot128\); the multiplicative-order identities supply its odd part. Hence \(2^n\bmod(b\cdot49\cdot128)\), and therefore \(u\bmod(49\cdot128)\), are constant along each progression. The same holds for \(P\bmod(49\cdot128)\).

From the restart formulas, increasing \(h\) by one therefore shifts the start residues by

\[
\begin{array}{c|ccc}
& D_R & m_R & N_0\\\hline
\mathrm{I}&+32&+32&+32\\
\mathrm{II}&-32&-32&-32
\end{array}
\qquad(\bmod128).
\]

Four increments return to the same residues. The four residue triples are:

| Family | \(h\bmod4\) | \(D_R\bmod128\) | \(m_R\bmod128\) | \(N_0\bmod128\) |
|---|---:|---:|---:|---:|
| I | 0 | 36 | 117 | 21 |
| I | 1 | 68 | 21 | 53 |
| I | 2 | 100 | 53 | 85 |
| I | 3 | 4 | 85 | 117 |
| II | 0 | 124 | 49 | 117 |
| II | 1 | 92 | 17 | 85 |
| II | 2 | 60 | 113 | 53 |
| II | 3 | 28 | 81 | 21 |

## Exhaustive finite-graph result

The self-contained checker [root_prefix_mod128.js](root_prefix_mod128.js) constructs the start residues using exact BigInt modular arithmetic, computes the complete reachable closure in the 16,384-vertex graph, and separately checks that the computed set is successor-closed under all 134 edge labels.

For the four excluded cases:

| Family | \(h\bmod4\) | Reachable vertices | Root \((2,0)\) in closure? | FNV-1a fingerprint of 16,384-byte membership vector |
|---|---:|---:|---|---|
| I | 0 | 1,384 | No | 1f9864d28e1b3da5 |
| I | 3 | 1,384 | No | 7b214ef39db40325 |
| II | 0 | 1,384 | No | 7b214ef39db40325 |
| II | 3 | 1,384 | No | 1f9864d28e1b3da5 |

The repeated fingerprints reflect two identical finite closures shared across the four start cases; the checker independently reconstructs and closure-checks each case.

## Consequence and limitations

For both arithmetic restart families, when \(h\equiv0\) or \(3\pmod4\), the restart state has **no reverse-parent path to the P1 blank root**, even in the deliberately enlarged graph that permits every positive inverse cost. Therefore the corresponding synthetic fourth-edge suffix cannot be attached to the authentic blank-start orbit.

This is an independent root-prefix obstruction; it does not use the wall subset-sum carry condition or the high-cost prefix budget. It closes half of the two local-survivor progressions at the root-correspondence stage.

For \(h\equiv1,2\pmod4\), this modulo-128 graph does contain the root vertex in its start closure, so this modulus supplies no exclusion. That is only failure of this necessary-condition sieve, not evidence of an actual root path. The other P1 inverse exits and the complementary parameter classes remain open.

