# Exact inverse-spine structure for #746 halting gates

**Status:** two algebraic statements over the exact original-source `ResetParent` grammar: (i) the existing narrow-window t=0 entry embedding into a *single* even-spine branch, and (ii) a new all-sector, all-index **exact criterion for predecessor existence at the canonical spine's terminal state**. The complete derivations are paper proofs, not yet compiled against the original source in Lean. Neither statement eliminates off-spine odd-parent forks or decides the machine.

## 1. Actual source gate

`OriginalAlgorithmicGate.lean` gives the exact criterion
[
\text{#746 halts}\iff
\exists n\ge257,\ n\bmod6\in\{4,5\},\operatorname{ReachC}(2,0)(U_n,0),
\qquad U_n=4\cdot2^n-n-4.
]
Write (n=K+2) and (p=2^K). Then
[
U_{K+2}=16p-K-6.
]

The following construction identifies one explicit inverse-parent branch of this actual target with the auxiliary t=0 entry family already studied in this directory.

## 2. Exact parent-chain identity

Put
[
c=2K+7,\qquad J=K+2-a,\qquad
B=c\,2^{K+4-a},\qquad
N=B+2K+1-16p,
]
and define
[
E(a,K)=8p+K-\frac N3
       =\frac{40p+K-1-B}{3}.
]
Assume
[
K\ge5,\quad J\ge1,\quad
\frac{97}{64}\le x:=\frac{c}{2^a}\le\frac{13}{8},
\quad N\equiv0\pmod3.
]
For (0\le j\le J), define the spine states
[
u_j=16p+K+1-c2^j.
]
Then (u_0=16p-K-6=U_{K+2}).

### Even-parent steps

For (j<J),
[
u_{j+1}=2u_j-16p-(K+1).
]
Also (B=c2^{J+2}), so
[
c2^j\le c2^{J-1}=B/8\le13p/4.
]
Consequently
[
u_j\ge16p+K+1-13p/4
       =51p/4+K+1>12p-1.
]
Since (u_j\le u_0=16p-K-6\le16p-3), every child (u_j) lies in the even-parent band
[
12p-1\le u_j\le16p-3
]
at level (K+1). The exact even-parent equation is
[
2u_j=16p+(K+1)+u_{j+1},
]
hence (operatorname{ResetParent}(u_{j+1},u_j)) for all (j<J).

### Terminal odd-parent step

At the end of the spine,
[
u_J=16p+K+1-B/4,qquad
X_J:=2u_J+5=32p+2K+7-B/2.
]
The divisibility assumption (N\equiv0\pmod3) implies (3\mid X_J): indeed
[
2X_J=64p+4K+14-B
\equiv48p+6K+15\equiv0\pmod3,
]
using (B\equiv16p-2K-1\pmod3). Let (d=X_J/3). Since (X_J) is odd, (d) is odd.

The window gives (B=16xp\in[(97/4)p,26p]). Therefore
[
d=\frac{32p+2K+7-B/2}{3}.
]
The upper bound (B\le26p) gives
[
d\ge\frac{19p+2K+7}{3}\ge6p+1.
]
For the other side, (B\ge(97/4)p) gives
[
3d\le\frac{159}{8}p+2K+7\le24p-3,
]
where the last inequality is (33p\ge16K+80), valid for (K\ge5). Thus
[
6p+1\le d\le8p-1.
]
This is exactly the odd-source band at level (K), with (t=0). Its parent is
[
egin{aligned}
h&=2d-8p-K-5\\
 &=\frac{40p+K-1-B}{3}\\
 &=8p+K-\frac{B+2K+1-16p}{3}\\
 &=E(a,K).
end{aligned}
]
Hence (operatorname{ResetParent}(E(a,K),u_J)).

Combining this edge with the (J) even-parent edges yields the exact chain
[
\boxed{\operatorname{ResetChain}(E(a,K),U_{K+2})}.
]
The chain has (J) even-parent edges followed by one odd (t=0) edge.

## 3. The parameter (a) is determined by the gate target on this branch

For a fixed (K), the t=0 source coordinate at spine state (u_j) is
[
d_j=\frac{2u_j+5}{3}
=\frac{32p+2K+7-2c2^j}{3}.
]
Its exact level-(K) odd-band condition
[
6p+1\le d_j\le8p-1
]
is equivalent to
[
4p+K+5\le c2^j\le7p+K+2.
]
The ratio of the right endpoint to the left endpoint is less than (2), so there is at most one integer (j) satisfying this condition. If it exists, then
[
a=K+2-j
]
is uniquely determined and (B=c2^{j+2}). Equivalently, the exact x-window for this t=0 source-band condition is
[
1+\frac{K+5}{4p}
\le x\le
\frac74+\frac{K+2}{4p},
]
together with the required divisibility (3\mid2u_j+5).

Thus the t=0 entry parameter is not independent on the main spine: it is the unique dyadic index of the terminal t=0 source-band crossing, when such a crossing exists.

For the two actual gate residue sectors, the divisibility condition itself forces the parity. Since
[
X_j=2u_j+5=32p+2K+7-2c2^j,
]
if (K\equiv2\pmod6), then (p\equiv1), (c\equiv2\pmod3), and
(X_j\equiv1-2^j\pmod3); if (K\equiv3\pmod6), then (p\equiv2), (c\equiv1\pmod3), and (X_j\equiv2-2^{j+1}\pmod3). In either case (3\mid X_j) exactly when (j) is even. Hence (a=K+2-j) has the same parity as (K): even (a) for the (n\equiv4\pmod6) gate sector, odd (a) for (n\equiv5\pmod6).

## 4. Exact all-index classification of the terminal spine state

This result uses **no narrow x-window**. Fix every n≥257 with n mod 6∈{4,5}. Put
\[
  c=2n+3,\quad a=\lfloor\log_2c\rfloor,\quad p=2^n,\quad
  J=n-a,\quad s=2^J,\quad q=cs,
\]
and continue the same canonical ray \(u_j=4p+n-1-c2^j\) to \(u_J\).
Equivalently \(2^a\le c<2^{a+1}\). Since \(c\) is odd,
\(r=c-2^a\) is a **positive** integer and \(q=p+rs<2p\).

**Terminal predecessor theorem (paper proof).** Let \(X=2u_J+5\). With
\(\mathrm{ResetParent}\) defined *exactly* as in `FirstInverseComplete.lean`,
\[
\boxed{\quad
  (\exists h:\mathbb N,\ \mathrm{ResetParent}(h,u_J))
  \ \Longleftrightarrow\
  (J\equiv0\pmod2)
  \ \land\
  \bigl(4c\le7\cdot2^a\ \lor\ X\equiv0\pmod9\bigr).\quad}
\]
Thus the complement is an **actual predecessor-free leaf**, not merely
the absence of an arbitrarily selected “maximal-valuation” parent.

**Uniform gap proof.** The elementary inequality
\(2^n>(n+4)(2n+3)\), valid for all \(n\ge10\) (base case and
induction under doubling), implies \(s>n+4\).
Using \(q=p+rs\) and \(p\le q<2p\), one obtains
\[
   2p<u_J=3p+n-1-rs<3p-1.
\]
For every \(k\le n-2\), the even-parent target band ends by
\(8\cdot2^k-3\le2p-3<u_J\); for every \(k\ge n-1\) it begins at
\(6\cdot2^k-1\ge3p-1>u_J\). Therefore **no even ResetParent exists**,
with no exceptional dyadic scale.

**Odd branches and exact converse.** The original odd-parent grammar is
\[
  2u_J+5=3^{t+1}d,\quad d\equiv1\pmod2,\quad
  6\cdot2^k+1\le2^td\le8\cdot2^k-1,\quad
  h=2^{t+1}d-8\cdot2^k-k-5\ge0.
\]
Its first equation requires \(3\mid X\). The signed canonical-ray
identity or a two-case computation modulo 3 gives
\(3\mid X\iff J\) is even for both surviving gate sectors.
If \(J\) is odd, **every odd t is impossible**.

Suppose \(J\) is even. Then \(3\mid X\), and \(d_0=X/3\) is odd.
For \(t=0\), the only possible source scale is \(k=n-2\):
the terminal gap implies \(p<d_0<2p\), excluding all other k.
The upper source-band inequality \(d_0\le2p-1\) holds automatically,
and the lower one is exactly
\[
  d_0\ge3p/2+1\quad\iff\quad 4q\le7p+4n.
\]
Since \(q=cs\), \(p=2^as\), \(a\ge2\), and \(s>n+4\),
\[
  4q\le7p+4n\quad\iff\quad4c\le7\cdot2^a.
\]
Indeed a positive value of \(4c-7\cdot2^a\) is a positive multiple
of four, making \(4q-7p\ge4s>4n+15\).
When the inequality holds, the concrete parent is
\[
  h_0=2(X/3)-2p-n-3,
\]
which is nonnegative by the same source-band lower bound.

In the complementary high-c case \(4c>7\cdot2^a\), \(t=0\) is
impossible at **every** scale, and
\(4q\ge7p+4n+16\). If \(9\mid X\), take \(t=1\), \(d_1=X/9\),
\(k=n-3\). Its source band is
\[
  3p/4+1\le 2X/9\le p-1.
\]
The lower inequality follows from \(u_J>2p\), and the upper one
from \(4q\ge7p+4n+16\); the corresponding
\(h_1=4(X/9)-p-n-2\) is nonnegative for \(n\ge257\).
Thus \(9\mid X\) supplies an **actual** t=1 parent, even when X has
higher 3-adic valuation. If \(9\nmid X\), all \(t\ge1\) are excluded
by their output divisibility \(9\mid X\), while \(t=0\) has already
failed. This proves the equivalence in both directions, without
discarding any lower-valuation possibilities.

**Residues and density within dyadic blocks.** In the \(J\)-even
part of each block \(2^a\le2n+3<2^{a+1}\), the condition \(9\mid X\)
occupies precisely one of the three \(n\bmod18\) classes in the
relevant n mod 6 sector. More explicitly,
\[
\begin{array}{ll}
a\ {\rm even},\ n\bmod6=4:&9\mid X\iff n\equiv3a+10\pmod{18},\\
a\ {\rm odd},\ n\bmod6=5:&9\mid X\iff n\equiv2-3a\pmod{18}.
\end{array}
\]
This follows by reducing \(X=8\cdot2^n+2n+3-2c2^{n-a}\)
modulo 9, using the period 6 of \(2^j\bmod9\).
Within one complete block, half the eligible gate indices have
\(J\) odd. Among the other half, the high-c tail
\(4c>7\cdot2^a\) occupies one quarter of the index interval,
and \(9\nmid X\) selects two out of three compatible residues.
Consequently the **exact predecessor-free terminal fraction**, over
all eligible gate n within block a, tends to
\[
  \frac12+\frac12\cdot\frac14\cdot\frac23
  =\boxed{\frac7{12}}\qquad(a\to\infty),
\]
with \(O(1)\) counting error per block. Across *prefixes* n≤N this fraction has no single natural
density. Write \(N=t2^a\), \(t\in[1/2,1]\), with an \(O(1)\) boundary
adjustment to stay in the same dyadic block. Completed smaller
blocks contribute \(2^a/72+O(a)\) extra terminal leaves beyond the
baseline parity-half; the current block contributes
\(2^a(t-7/8)_+/9+O(1)\), where \(x_+=\max(x,0)\).
Since the number of surviving gate indices up to N is \(N/3+O(1)\),
the relative leaf fraction is
\[
 \frac12+\frac1{24t}+\frac{(t-7/8)_+}{3t}+o(1).
\]
It has liminf \(23/42\) (at the high-c threshold \(t=7/8\))
and limsup \(7/12\) (at complete block endpoints \(t=1\) or \(1/2\)). These densities describe **one terminal inverse
spine state per gate index**, not halting machines, valid target
exclusions, or blank-root nonreachability.

The independent full-grammar exact-integer regression is
[`terminal_spine_parent_census.mjs`](terminal_spine_parent_census.mjs).
It is a finite consistency test; the quantified proof is the
inequality-and-divisibility argument above.

## 5. Where the current E-parent results apply

The even-parent bands adjacent to (E) are
[
[3p-1,4p-3]\quad(k=K-1),\qquad
[6p-1,8p-3]\quad(k=K).
]
Therefore (E) has no even parent whenever
[
4p-3<E<6p-1.
]
Substituting (E=(40p+K-1-16xp)/3), this is equivalent to
[
\frac{11}{8}+\frac{K+2}{16p}
<x<
\frac74+\frac{K+8}{16p}.
]
The existing t=0/q=0 exclusion work uses the narrower window
[
97/64\le x\le13/8,
]
which lies strictly inside this no-even-parent interval. It does not cover the entire main-spine t=0 source-band window.

The parity sectors align with both original gate residues:
- (K\equiv2\pmod6), (a) even: (K+4-a) is even, (N\equiv0\pmod3), and (n=K+2\equiv4\pmod6).
- (K\equiv3\pmod6), (a) odd: (K+4-a) is even, (N\equiv0\pmod3), and (n=K+2\equiv5\pmod6).

The odd-a, (K\equiv3\pmod6) entry-parent classification remains open.

## 6. Existing Ray reductions to compose, not duplicate

The spine formula above is the same canonical even ray used by the repository's `Ray*` modules:
[
u_j=4\cdot2^n-\big((2n+3)2^j-(n-1)\big),\qquad n=K+2.
]
These existing source-connected results already classify substantial parts of the odd-parent side-branch problem:

- `RayPacketHigh.lean` and `RayTwoTierSelector.lean` reduce rooted odd forks on the high-margin ray to (t\ge2) or exceptional (t=1) congruence gates.
- `RayOddForkExtended.lean` and `RayForkStripSelect.lean` handle high-margin (t=0) exclusion and (t=1) fork selection.
- `RayTThreePacket.lean`, `RayTThreeHighRoot.lean`, `RayTThreeLowRoot.lean`, `RayTThreeDoubleSelector.lean`, and `RayThirdGate.lean` cover (t=3) and related two-gate branches under their stated hypotheses.
- `RayNoSeam.lean`, `RayNoSeamRoot.lean`, and `RayNoSeamResidue.lean` address weak-margin/no-seam and second-tier (t=1) cases.
- `RayTwoTierDepthHensel.lean` and `RayTwoTierIndexHensel.lean` give exact 3-adic divisibility selectors and unique Hensel lifts.
- `FatalOddFeederCriterion.lean` and `RayTwoGateExact.lean` give additional (t=1) odd-feeder and off-ray reductions.

These are conditional local reductions, not yet a proved exhaustion of every side branch along the complete (u_j) spine. The new t=0 embedding identifies the terminal main-spine branch; the next task is to compose the existing Ray reductions with the exact (u_j) indices, account for the terminal weak-margin window, and state precisely which branches/phase cases remain uncovered. Reimplementing these modules would be redundant.

### Exact length of the terminal weak-margin tail in the current x-window

The high-margin hypothesis used by `RayTwoTierSelector.lean` is
[
2048\,\operatorname{deficit}(n,j)+16384n+16384\le2^n,
\quad \operatorname{deficit}(n,j)=(2n+3)2^j-(n-1).
]
Here (J=K+2-a=n-a) and (c2^J=x2^n). At (j=J-12), the left side is exactly
[
(x/2)2^n+14336n+18432,
]
which is at most (2^n) for (x\le13/8) and (n\ge257). At (j=J-11), it is
[
x2^n+14336n+18432>2^n
]
because (x\ge97/64>1). The expression is increasing in (j), so the high-margin condition holds for every (j\le J-12) and fails for every (j\ge J-11).

Therefore, for the current x-window, the high-margin Ray reductions cover the spine through (J-12), and the terminal weak-margin tail consists of exactly the twelve indices
[
J-11,J-10,\ldots,J.
]
This gives a concrete finite target for composing `RayNoSeam`, `RayNoSeamWalk`, the two-tier Hensel selectors, and the terminal t=0 entry (E(a,K)). The BigInt checks at ((K,a)=(387,9),(800,10),(399,9),(806,10)) independently found this exact 12-index split; the algebra above explains it uniformly.

## 7. Scope and remaining work

This identity connects the auxiliary entry family to the actual #746 halting targets. It proves that (E(a,K)) is an ancestor on **one** inverse-parent branch of (U_{K+2}). It does **not** prove that every root path to (U_{K+2}) passes through (E(a,K)). Other odd-parent side branches can leave intermediate spine nodes; a root path could in principle enter through one of them.

The following are still required for a global #746 conclusion:

1. Formalize the chain identity and the new terminal predecessor theorem against the exact `ResetParent` and `ResetChain` definitions in Lean.
2. Compose the existing Ray reductions listed above with every (t\ge1) side branch leaving the intermediate (u_j), and prove the hypotheses exhaust the full spine (or identify the uncovered cases).
3. Extend the E-parent exclusions beyond the current narrow x-window and across the remaining parity/phase sectors.
4. Combine the branch classifications with `OriginalAlgorithmicGate.lean` to exclude every (n\ge257) with (n\bmod6\in\{4,5\}).

Exact BigInt checks were made for representative pairs including ((K,a)=(387,9)) and ((800,10)), yielding the predicted (J+1)-edge chain. These are consistency checks only; the algebraic derivation above is the substantive claim, and the Lean formalization is pending. No #746 nonhalting or BB(6) conclusion is claimed.
