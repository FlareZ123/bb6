# Seventh Sheep stratum: candidate finite inverse-tree progression

**Agent 17, 20 November 2026. This 15-node mixed-parent family is included in the accepted five-family theorem, compiled in [CI 45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209) with Lean 4.36.0-rc2.**

This note extends the exact direct-parent census in [`certificate.py`](certificate.py). It does not replace the original Sheep transition relation by a surrogate. The proof strategy uses the arbitrary-edge source split in Agent 14's `SheepEvenSourceAlgebra.even_edge_to_algebra` and the last-edge decomposition of `EvenReach`.

## Accepted subfamily theorem

Let
[
T=32,526,940,446,000
=2^4\cdot3^7\cdot5^3\cdot7\cdot11\cdot13\cdot17\cdot19\cdot23.
]
The exact affine inverse-tree certificate supports the all-time statement
[
\boxed{\forall k\ge0,\quad
\neg\operatorname{EvenReach}\bigl(10,2^{1458(1+Tk)}\bigr).}
]

Equivalently, the exponent indices
[
j=1458+47,424,279,170,268,000,k
]
are unreachable from the authentic blank-even entry 10.

This family is now included in the compiled `SheepPower1458.noEvenReachFiveFamilies` theorem from [CI 45293408209](https://github.com/FlareZ123/bb6/actions/runs/45293408209), whose transitive axiom profile is `[propext, Classical.choice, Quot.sound]` and contains no `sorryAx`. It remains a partial exclusion of one exponent progression, not a Sheep machine or BB(6) decision. Keep it in `im-results/`.

## Why direct-parent exclusion is insufficient

The previous seventh-stratum theorem `blank_even_cannot_hit_seventh` excludes targets only when
[
3\nmid t,\quad 4\mid t,\quad
t\not\equiv5\pmod7,\quad
t\not\equiv1\pmod9,\quad
t\not\equiv8\pmod{15}.
]
The new class has (t\equiv1\pmod T), so it has genuine direct parents. The argument instead enumerates their complete inverse ancestry and proves that every branch terminates at a state with no predecessor.

## Original-source inverse equations

For every actual `EvenEdge x y`, the existing theorem
`SheepEvenSourceAlgebra.even_edge_to_algebra` gives exactly one of:

**Generic source**
[
y=1+3^h u,\quad u\text{ odd},\quad
x=2^a v,\quad a\ge1,\quad v\ge5\text{ odd},
]
with
[
(2^{a+1}+1)v=2^{h+1}u+3-2a.
]

**Exceptional source**
[
y=1+3^h u,\quad u\text{ odd},\quad
x=3\cdot2^a,\quad a\ge1,
]
with
[
2^h u=3\cdot2^a+a+2.
]

No rational-power hypothesis on (y) is needed. This is important because the intermediate inverse-tree nodes are not generally powers of two.

## Affine node representation

Write (j=1458t). Every node in the inverse tree is represented by
[
Y(t)=\frac{2^{j+s}+B}{C},
]
where (s\in\mathbb N), (B\in\mathbb Z), and (C\) is a positive odd integer. At (t=1), every listed node is an even integer greater than 10.

Let
[
r=v_3(Y(1)-1).
]
For a possible predecessor, (h) ranges over (0\le h\le r). Put (D=C3^h). The generic source equation becomes
[
D(2^{a+1}+1)v+K(a)=2^{j+s+h+1},
]
where
[
K(a)=2^{h+1}(C-B)+D(2a-3).
]
Thus a generic predecessor with valuation (a) exists exactly when
[
D(2^{a+1}+1)\mid 2^{j+s+h+1}-K(a),
]
and the quotient (v) is at least 5.

If such a predecessor exists, its next affine node is
[
s'=s+a+h+1,
]
[
B'=2^a\bigl(2^{h+1}(B-C)+C3^h(3-2a)\bigr),
qquad
C'=D(2^{a+1}+1).
]

### Uniform generic high-valuation cutoff

The function (K(a)) is odd and
[
K(a+1)=K(a)+2D.
]
For each node and each (0\le h\le r), the certificate supplies a cutoff (A) such that
[
1<K(A)<2^A,\qquad 2D\le2^A.
]
These inequalities persist for every (a\ge A). Consequently (1<K(a)<2^a) for all such (a), and the existing signed-power gap theorem
`SheepOddGap.no_power_signed_small_odd` rules out
[
2^{a+1}+1\mid 2^{j+s+h+1}-K(a).
]
Therefore only the finite range (1\le a<A) needs modular checking.

The 31 generic cutoffs are:

| Node | Allowed (h) and cutoff (A) |
|---:|---|
| 0 | 0:2, 1:5, 2:7, 3:9, 4:11, 5:13, 6:15, 7:16 |
| 1 | 0:8, 1:10 |
| 2 | 0:12, 1:14 |
| 3 | 0:16, 1:17 |
| 4 | 0:19 |
| 5 | 0:20 |
| 6 | 0:14, 1:16, 2:17 |
| 7 | 0:15, 1:16, 2:18, 3:20 |
| 8 | 0:17, 1:19 |
| 9 | 0:20 |
| 10 | 0:23 |
| 11 | 0:23 |
| 12 | 0:23 |
| 13 | 0:25 |
| 14 | 0:26 |

### Exceptional source exclusion: uniform divisibility gap

For every node \(Y(t)=(2^{1458t+s}+B)/C\), the exceptional source equation is
\[
3D2^a+D(a+2)+S=2^N,\qquad
D=C3^h,\quad S=2^h(C-B),\quad N=1458t+s+h.
\]
For this 15-node tree and every allowed \(0\le h\le r\), the exact node table gives
\[
1\le D\le885735,\qquad 0<S\le3321979,\qquad N\ge1458.
\]
Use the common bound \(M=4{,}000{,}000\).

If \(a\le31\), then
\[
3D2^a+D(a+2)+S
\le12{,}000{,}000\cdot2^{31}
  +4{,}000{,}000\cdot33+4{,}000{,}000
<2^{55}\le2^N.
\]
If \(a\ge32\), put \(L=D(a+2)+S\). At \(a=32\),
\[
0<L\le4{,}000{,}000\cdot34+4{,}000{,}000
=140{,}000{,}000<2^{32}.
\]
Since \(D\le4{,}000{,}000<2^{32}\le2^a\), the recurrence \(L(a+1)=L(a)+D\) proves \(0<L<2^a\) for all \(a\ge32\).

If \(a>N\), then \(3D2^a>2^N\), contradiction. If \(a\le N\), then \(2^a\) divides both \(2^N\) and \(3D2^a\), so the equation forces \(2^a\mid L\), contradicting \(0<L<2^a\).

Thus no exceptional parent exists at any node, for any \(a\), and the 31 per-node special cutoffs are unnecessary as proof dependencies. They remain in the Python certificate as redundant diagnostics. This replaces the former \(e,z\) case split with a shorter 2-adic divisibility argument.
## Complete affine inverse graph at (t=1)

The exact graph has 15 nodes and 14 generic edges. A node ID represents
[
Y_i(t)=\frac{2^{1458t+s_i}+B_i}{C_i}.
]
The column (r) is (v_3(Y_i(1)-1)).

| ID | (s_i) | (B_i) | (C_i) | (r) | All possible generic parents ((h,a)\to\text{ID}) |
|---:|---:|---:|---:|---:|---|
| 0 | 0 | 0 | 1 | 7 | (1,1)→1; (3,1)→2; (5,1)→3; (7,1)→4; (7,2)→5 |
| 1 | 3 | -2 | 15 | 1 | (1,2)→6 |
| 2 | 5 | 22 | 135 | 1 | (0,1)→7; (1,2)→8 |
| 3 | 7 | 358 | 1215 | 1 | (0,3)→9 |
| 4 | 9 | 3862 | 10935 | 0 | none |
| 5 | 10 | -9772 | 19683 | 0 | (0,1)→10 |
| 6 | 7 | -452 | 405 | 2 | none |
| 7 | 7 | -182 | 675 | 3 | none |
| 8 | 9 | -3428 | 3645 | 1 | (1,2)→11 |
| 9 | 11 | -42872 | 20655 | 0 | (0,1)→12 |
| 10 | 12 | -78454 | 98415 | 0 | (0,1)→13 |
| 11 | 13 | -156908 | 98415 | 0 | (0,2)→14 |
| 12 | 13 | -212798 | 103275 | 0 | none |
| 13 | 14 | -510646 | 492075 | 0 | none |
| 14 | 16 | -2436244 | 885735 | 0 | none |

The six terminal leaves are
[
\boxed{4,6,7,12,13,14}.
]
Every leaf has no generic parent, and the exceptional-source argument excludes every special parent. All 14 displayed edges have a positive odd cofactor (v\ge5) at (t=1).

## Why the same graph holds for (t\equiv1\pmod T)

For every node, the certificate freezes (v_3(Y(t)-1)) by a period modulo
[
3^{r+v_3(C)+1}.
]
For every node, every (0\le h\le r), and every (1\le a<A), it computes the exact multiplicative order of 2 modulo
[
N=C3^h(2^{a+1}+1).
]
If (o_N=\operatorname{ord}_N(2)), then the period of (2^{1458t}) modulo (N) is
[
p_N=o_N/\gcd(o_N,1458).
]
The common period (T) is the LCM of all 455 such periods and the 15 valuation-freezing periods. The exact arithmetic checker verifies
[
2^{1458T}\equiv1\pmod N
]
for every one of the 455 moduli and for every valuation-freezing modulus.

Thus for (t=1+Tk), every node has the same 3-adic valuation range and every finite generic divisibility test has exactly the same outcome as at (t=1). A successful row remains a valid parent because its quotient is already odd and at least 5 at (t=1), and increases with (t). A failed row remains impossible. The high-(a) signed-power cutoffs and exceptional-source argument are uniform in (t\ge1).

The exact certificate reports:

- 15 affine nodes and 14 generic edges;
- 455 exact modular periods;
- 15 3-adic valuation-freezing periods;
- 31 generic and 31 exceptional cutoffs;
- maximum generic cutoff 26 and maximum exceptional cutoff 25;
- (T=32,526,940,446,000) with the factorization above.

## Blank-root contradiction

Suppose `EvenReach 10 (Y_0(t))` for (t=1+Tk). Since (Y_0(t)>10), the existing last-edge theorem yields a genuine earlier state (x) with `EvenReach 10 x` and an original `EvenEdge x (Y_0(t))`. Even reachability preserves evenness, so `even_edge_to_algebra` applies. The generic/special analysis forces (x) to be one of the listed children. Repeating the same argument moves strictly down the finite inverse graph until it reaches one of the six leaves. But those leaves have no incoming original even edge of either type. Contradiction.

This is an all-time argument; it does not impose a trajectory horizon or assume that synthetic inverse states are reachable from 10.

## Nonoverlap and scope

The progression is disjoint from the 28 explicit earlier E-cone progressions in the existing direct-census certificate. For each old progression (j\equiv b\pmod p), the base exponent (1458) is not congruent to (b) modulo (p), and (T) is a multiple of (p/\gcd(p,1458)), so the entire new progression stays disjoint.

The fourth/fifth strata (j=54m) and (j=162m) have (v_3(j)=3,4), respectively; the eighth stratum (j=4374t), (3\nmid t), has (v_3(j)=7). They are disjoint from this (v_3(j)=6) progression.

This is one very sparse infinite class (density (1/47,424,279,170,268,000) among all exponent indices). It does not decide the Sheep machine, the remaining seventh-stratum exponents, or BB(6). The key next step is an independent local Lean 4.36.0-rc2 proof against the pinned original Sheep source, with `#print axioms` on the final blank-root theorem and no `sorryAx`.
