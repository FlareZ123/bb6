# Exact inverse-spine structure for #746 halting gates

**Status:** ten algebraic statements over the exact original-source `ResetParent` grammar: (i) the existing narrow-window t=0 entry embedding into a *single* even-spine branch, (ii) an all-sector, all-index **exact criterion for predecessor existence at the canonical spine's terminal state**, (iii) a full **unique-chain root-exclusion** on a low-valuation terminal subfamily, and (iv) a two-edge exclusion in a second low-valuation sector, and (v) a disjoint four-edge exclusion in its next dyadic-depth window, and (vi) a forced second-tier odd-parent fork in a further infinite narrow high-c strip, and (vii) a complete nonterminal off-spine fork cone two indices closer to the actual gate, extended by six forced-even levels, and (viii) a second complete off-spine fork giving a 17-node root-dead cone thirteen inverse levels nearer the gate, and (ix) a nine-packet Hensel obstruction forcing t=3 odd-parent forks in a high-c terminal phase, and (x) the stronger unconditional **all-surviving-gate primitive-root theorem**, forcing a genuine three-parent/t=3 fork in the first 54 canonical inverse states of every original #746 halting gate. The complete derivations are paper proofs, not yet compiled against the original source in Lean. Neither statement eliminates off-spine odd-parent forks or decides the machine.

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

## 5. Uniform exclusion of low-valuation terminal branches

The preceding terminal theorem is only a predecessor-existence classification.
The following stronger result decides genuine blank-root reachability for an
additional infinite **terminal-state subfamily whose terminal states do have
predecessors**. This remains a paper proof over the exact full parent grammar;
it is not yet a Lean-compiled source theorem.

**Theorem (complete inverse cone).** Keep \(n\ge257\), \(n\bmod6\in\{4,5\}\)
and the notation \(c,a,J,s,p,q,u_J,X\) of Section 4. Suppose
\(J\) is even and \(4c>7\cdot2^a\). If additionally
\[
 \begin{cases}
 X\bmod27\in\{9,18\},& n\bmod6=4,\\
 X\bmod27=9,& n\bmod6=5,
 \end{cases}
\]
then the **entire inverse ResetParent cone of \(u_J\)** is a finite,
unique chain ending in a parentless state different from 2. In particular
\[
 \neg\operatorname{ResetChain}(2,u_J),\qquad
 \neg\operatorname{ReachC}((2,0),(u_J,0)).
\]
The latter uses the existing source-certified equivalence in
ResetChain.lean; the new parametric proof itself is not yet formalized.
This closes **one inverse branch** of \(U_n\), not the off-spine odd
forks from earlier \(u_j\), and does not prove #746 nonhalting.

**First inverse step.** Section 4 rules out every even parent and
every odd valuation \(t=0\) in the high-\(c\) window. Since
\(v_3(X)=2\), valuations \(t\ge2\) are impossible as well.
The only parent is the \(t=1\) parent at scale \(k=n-3\),
\[
 b_0=4(X/9)-p-n-2=\frac{23p-8q-n-6}{9}.
\]
Its output-band interval is
\[
 3p/4-1\le b_0\le p-3.
\]
Indeed \(q>7p/4\) gives the upper bound and
\(q<2p\) gives \(b_0>(7p-n-6)/9>3p/4-1\),
using \(p>4n\). Hence \(b_0\) has a unique possible
even-parent scale \(k=n-3\), and the only alternative
parents would be odd parents.

**Residue obstruction for every subsequent odd parent.** An
even predecessor at \(k=n-3\) has exact recurrence
\[
 b\longmapsto b'=2b-p-(n-3).
\]
For \(n\bmod6=4\), \(p\equiv n\equiv1\pmod3\);
the two allowed \(X\bmod27\) residues give
\(b_0\bmod3\in\{0,1\}\), and the recurrence
\(b'\equiv1-b\pmod3\) preserves \(\{0,1\}\).
For \(n\bmod6=5\), \(p\equiv n\equiv2\pmod3\);
\(X\bmod27=9\) gives \(b_0\equiv1\pmod3\), and
\(b'\equiv2-b\equiv1\pmod3\).
Thus at every finite depth on the even spine,
\(b\bmod3\ne2\), equivalently \(3\nmid(2b+5)\).
**All odd-parent valuations are ruled out at once**, including
lower valuations that prior maximal-valuation-only analyses omitted.

**The exit cannot cross the next even-image seam.** Define
\[
 \delta=4c-7\cdot2^a,\quad 4\le\delta<2^a,\quad
 \delta\equiv4\pmod8,\qquad
 D_0=p-b_0=\frac{2\delta s+n+6}{9}.
\]
Here \(\nu_2(\delta)=2\). Along the unique even-parent chain,
as long as the \(k=n-3\) target band holds,
\[
 b_{e+1}=2b_e-p-(n-3),\quad
 D_{e+1}=2D_e+(n-3),\qquad
 9D_e=2^e(2\delta s+10n-21)-9(n-3).
\]
Since \(b_0>3p/4-1\), \(D_0<p/4+1\).
Let \(e\ge1\) be the first index with \(D_e>p/4+1\);
it exists by strict growth of \(D_e\).
The previous index lies in-band, so
\(D_e\le p/2+n-1\). The closed form, using \(e\ge1\),
also gives \(2^e\delta s\le9p/4-n+3\), so
\(2^e<2^a\) (because \(\delta\ge4\)).

We show \(D_e<p/2\). The elementary growth inequality
\(2^n>20n(2n+3)^2\) for \(n\ge257\) implies
\(s>20n2^a\). If instead \(D_e\ge p/2\), then
\(0\le9(D_e-p/2)\le9(n-1)\). But the exact identity is
\[
\begin{aligned}
 9(D_e-p/2)&=Cs+E,\\
 C&=2^{e+1}\delta-9\cdot2^{a-1},\\
 E&=2^e(10n-21)-9(n-3).
\end{aligned}
\]
Since \(1\le e<a\), \(0<E<10n2^a<s\).
If \(C\le-1\), then \(Cs+E<0\); if \(C\ge1\),
then \(Cs+E>s>9(n-1)\). Hence \(C=0\).
Taking 2-adic valuations, \(\nu_2(\delta)=2\)
forces \(e=a-4\) and \(\delta=36\). Consequently
\[
 c=7\cdot2^{a-2}+9,\qquad n=7\cdot2^{a-3}+3.
\]
For even \(a\), this gives \(n\bmod6=5\), making
\(J=n-a\) odd, contrary to the hypotheses. For odd \(a\),
it gives \(n\bmod6=1\), outside the surviving gate sectors.
Thus \(C\ne0\), a contradiction. Therefore
\[
     p/4+1<D_e<p/2,\qquad p/2<b_e<3p/4-1.
\]
The latter state is in the open gap between neighboring
even-target bands and has no even predecessor at *any*
scale. It has no odd predecessor by the established
mod-3 invariant. It is positive and different from the
blank root 2. Backward induction along the unique finite
parent chain proves the theorem.

**How much of the terminal branch is excluded?** Within each complete
dyadic index block \(2^a\le2n+3<2^{a+1}\), the Section 4
parentless leaf condition excludes a fraction approaching \(7/12\)
of surviving gate terminal states. Among the remaining indices,
the present theorem excludes another \(1/36\) for even \(a\),
or \(1/72\) for odd \(a\): over the high-\(c\), \(J\)-even
subblock, \(X\bmod27\in\{0,9,18\}\) cycles uniformly when the
index increases by 18, and the new theorem covers two of three
lifts for the \(n\bmod6=4\) sector, one of three for
\(n\bmod6=5\). The resulting **asymptotic terminal-branch
root-exclusion coverage** is
\[
 \begin{cases}
  11/18+O(2^{-a}),&a\ {\rm even},\\
  43/72+O(2^{-a}),&a\ {\rm odd}.
 \end{cases}
\]
This is a fraction of canonical *terminal inverse branches*,
**not** a fraction of machines or of actual gate targets
shown unreachable. All off-spine forks remain open.

A full-grammar exact-integer finite inverse-cone regression of the
low-valuation cases (22 qualifying n≡4 modulo 6 below 5000,
and 25 qualifying n≡5 modulo 6 below 15000) found 47/47 unique
chains ending in leaves, maximum observed depth six.
The all-parameter conclusion rests on the preceding algebra,
not on those finite checks.

## 6. An additional two-edge exclusion in the opposite low-valuation phase

The previous complete-chain theorem deliberately leaves the
\(n\bmod6=5\), \(X\bmod27=18\) case unresolved: its first predecessor
has residue 2 mod3, so an odd-parent fork could appear. A sizeable
explicit subfamily nevertheless has **exactly two inverse edges**.

**Theorem (two-edge terminal exclusion, paper proof).** In addition
to the Section 4 notation and gate assumptions, suppose
\[
  n\bmod6=5,\quad J\equiv0\pmod2,\quad
  64c\ge121\cdot2^a,\quad X\bmod27=18,
\]
and put
\[
 b_0=4(X/9)-p-n-2,\qquad Y=2b_0+5.
\]
If \(Y\bmod9\ne0\), then the complete inverse cone is exactly
\[
  u_J\ \longleftarrow\ b_0\
    \longleftarrow\ b_1,\qquad
  b_1=2b_0-p-(n-3),
\]
where \(b_1\ne2\) has **no** ResetParent. Consequently
\(\neg\operatorname{ReachC}((2,0),(u_J,0))\).

**Proof.** The ratio condition is \(q/p=c/2^a\ge121/64>7/4\),
so Section 5 proves the sole parent of \(u_J\) is the
t=1 parent \(b_0\), with \(3p/4-1\le b_0\le p-3\).
Now \(X\bmod27=18\), \(n\bmod6=5\) imply
\(b_0\bmod3=2\), hence \(3\mid Y\).
If \(b_0\) had an odd t=0 parent, its source parameter
would be \(d=Y/3\), which lies strictly between \(p/2\)
and \(3p/4\) because \(3p/4-1\le b_0\le p-3\).
This interval is a gap between the odd-source bands at
\(k=n-4\) and \(k=n-3\), and also misses all other
dyadic scales. Every t≥1 parent requires \(9\mid Y\),
which is ruled out by the hypothesis. Thus its only parent
is the even parent \(b_1\) at \(k=n-3\).

Let \(D_1=p-b_1\). The closed form from Section 5 gives
\[
 D_1=\frac{16q-28p+11n-15}{9}.
\]
With \(q\ge121p/64\) we get
\(D_1\ge p/4+(11n-15)/9>p/4+1\).
With \(q<2p\), we get
\(D_1<4p/9+(11n-15)/9<p/2\) since
\(2^n>22n\) for \(n\ge257\).
Therefore \(p/2<b_1<3p/4-1\), the open even-image gap,
so it has no even parent at any scale. Finally
\[
 b_1\bmod3
   =2b_0-p-(n-3)\equiv2\cdot2-2-2=0,
\]
so \(3\nmid(2b_1+5)\), eliminating all odd parents.
The unique cone terminates at \(b_1>p/2>2\).

**Uniform positive-density gain.** Within a complete dyadic
\(a\)-block for odd \(a\), the condition \(64c\ge121\cdot2^a\)
selects the final fraction \(7/64+O(2^{-a})\) of the block.
The even-J gate sector is \(n\bmod6=5\), a half of the
eligible gate indices. Within that sector
\(X\bmod27=18\) occupies one in nine index classes
(modulo 54), and among its three lifts modulo 162,
the exact shift \(Y(n+54)\equiv Y(n)+3\pmod9\) shows that
two in three satisfy \(Y\bmod9\ne0\). Thus this theorem adds
\[
   \frac12\cdot\frac7{64}\cdot\frac19\cdot\frac23
   =\frac7{1728}
\]
to the odd-\(a\) terminal branch exclusions. Combining
Sections 4–6 gives a lower-bound coverage fraction
\[
  \boxed{1039/1728+O(2^{-a})\ \approx0.601273}
\]
for odd \(a\), compared with \(11/18\) for even \(a\).
As above these are fractions of **one canonical terminal
inverse branch per eligible gate index**, *not* fractions
of actual fatal targets proved unreachable.

The conditions and exact chain can be reproduced directly
from the full grammar using the accompanying JS regression.
The proof remains uncompiled in Lean.

## 7. Four-edge root exclusion in the next dyadic depth window

A second, disjoint subfamily of the \(n\bmod6=5,X\bmod27=18\)
phase has a complete inverse chain of **four** edges rather than two.
This establishes that the strategy of combining even-chain
geometric depth with a small 3-adic residue invariant works beyond
the first band exit.

**Theorem (four-edge exclusion, paper proof).** Let the canonical
terminal state and \(b_0\) be as in Sections 4–6. Suppose
\[
 n\bmod6=5,\quad J\equiv0\pmod2,\quad
 X\bmod27=18,\quad b_0\bmod9=5,
\]
and the following strict dyadic strip conditions:
\[
 256c\ge457\cdot2^a,\qquad 128c<233\cdot2^a.
\]
Then the **complete** predecessor graph of \(u_J\) consists
of exactly the chain
\[
 u_J\leftarrow b_0\leftarrow b_1\leftarrow b_2
      \leftarrow b_3,
 \qquad b_{i+1}=2b_i-p-(n-3),
\]
and \(b_3\ne2\) is parentless. Hence
\(\neg\operatorname{ResetChain}(2,u_J)\) and source-equivalently
\(\neg\operatorname{ReachC}((2,0),(u_J,0))\).

**Proof.** The strip bounds imply
\(457/256\le q/p<233/128\), wholly inside
the high-\(c\) region \(7/4<q/p<2\).
As in Section 5, \(u_J\) has exactly the initial t=1
odd parent \(b_0\), which is in the \(k=n-3\)
even-target band. For every in-band \(b_i\), its
t=0 source \(d=(2b_i+5)/3\), when integral, lies
strictly between \(p/2\) and \(3p/4\), the
odd-source dyadic gap; any odd parent with t≥1
requires \(9\mid(2b_i+5)\).

The even predecessor recurrence modulo 3 gives
\(b_0,b_2\bmod3=2\) and \(b_1,b_3\bmod3=0\).
More precisely, put \(A=p+n-3\), which satisfies
\(A\equiv1\pmod3\), and note
\[
 b_2=4b_0-3A.
\]
Since \(b_0\bmod9=5\), we obtain
\(b_2\bmod9=4\cdot5-3\equiv8\pmod9\).
Thus at both even-index nodes \(b_0,b_2\),
the odd numerator is divisible by three but **not nine**;
all t≥1 odd parents are excluded. The odd-index
nodes have no odd parent at all by their mod-3 residues.

It remains to show that precisely the first three
even edges exist. With \(\delta=4c-7\cdot2^a\),
the closed form in Section 5 yields
\[
 9D_2=8\delta s+31n-57,\qquad
 9D_3=16\delta s+71n-141.
\]
The upper strict strip boundary and integrality imply
\[
 128q\le233p-128s,\quad
 \delta s=4q-7p\le(9/32)p-4s.
\]
Since \(s>n+4\), this gives \(D_2<p/4+1\),
so \(b_0,b_1,b_2\) all remain in the same
\(k=n-3\) even-target band.

The lower strip boundary gives
\(256q\ge457p\), whence
\(\delta s\ge(9/64)p\). Therefore
\(D_3>p/4+1\), so the chain exits at exactly
the third even edge. The universal no-overshoot proof
in Section 5 (whose gap-coefficient C=0 case is
forbidden in both surviving gate sectors with J even)
implies \(D_3<p/2\). Thus
\(p/2<b_3<3p/4-1\), an even-predecessor gap.
Finally \(b_3\bmod3=0\) eliminates every odd
predecessor. The chain terminates at a state \(>p/2>2\).

**Further arithmetic density:** the strip has width
\(233/128-457/256=9/256\) in \(c/2^a\).
For odd a, J-even selects half of eligible gate
indices; X%27=18 selects one class in nine; and the
additional b0%9=5 condition selects one of its
three exact n-mod-162 lifts. This adds an
asymptotic \(1/1536+O(2^{-a})\) disjoint
terminal-branch exclusion fraction. Including
Sections 4–7, the **odd-a** terminal-branch
exclusion fraction is therefore at least
\[
 \boxed{8321/13824+O(2^{-a})\approx0.601924}.
\]
The even-a bound remains 11/18. Again, earlier
off-spine odd forks are not excluded by this result.
The four-edge family is a paper proof awaiting
original-source Lean acceptance.

## 8. A forced odd-parent bifurcation at depth at most four

The previous low-valuation exclusions have the opposite
counterpart: close to the *lower high-c threshold*, the even
parent chain necessarily forks, for **every** compatible n
in a specified infinite parameter sector. This identifies
where a successful whole-gate exclusion must use the
multi-tier odd-parent machinery rather than a single-chain
argument.

**Theorem (uniform forced fork; paper proof).** Retain
\(n\bmod6=5\), \(J\) even, \(X=2u_J+5\),
\(X\bmod27=18\), require \(a\ge11\), and assume
\[
   7\cdot2^a<4c,\qquad 1024c<1801\cdot2^a.
\]
The initial odd t=1 predecessor \(b_0\) is unique.
Form \(b_{j+1}=2b_j-p-(n-3)\). Then all
\(b_0,\ldots,b_5\) lie in the \(k=n-3\)
even-target band, and **exactly one** of
\(b_0,b_2,b_4\) also has a genuine t=1 odd
ResetParent at source scale \(k=n-4\).
That odd parent is distinct from its even
parent. Thus the complete inverse cone of
\(u_J\) has a true bifurcation within the
first five ancestor states.

**Proof.** Put \(\delta=4c-7\cdot2^a>0\)
and \(s=2^{n-a}\). Because \(a\ge11\),
\(1024c<1801\cdot2^a\) and integrality give
\(1024q\le1801p-1024s\). Therefore
\[
  \delta s=4q-7p\le(9/256)p-4s.
\]
The closed forms of Section 5 at j=4,5 are
\[
 9D_4=32\delta s+151n-309,\qquad
 9D_5=64\delta s+311n-645.
\]
From the basic growth \(s>2n\) (valid for
n≥257), both imply
\[
 D_4<p/8,\qquad D_5<p/4+1.
\]
All earlier \(D_j\) are smaller, so
\(b_0,\ldots,b_5\) stay in the even-target
band and, moreover,
\[
 7p/8<b_0,b_2,b_4\le p-3.
\]

Let \(A=p+n-3\). In this gate sector
\(A\equiv1\pmod3\) while
\(b_0\equiv2\pmod3\) because \(X\bmod27=18\).
The exact even recurrence gives
\[
 b_{2i}\equiv A+4^i(b_0-A)\pmod9
 \quad(i=0,1,2).
\]
Since \(4^i\bmod9\) cycles through
\(1,4,7\), and \(b_0-A\equiv1\pmod3\),
the three residues \(b_0,b_2,b_4\)
are **exactly \(\{2,5,8\}\pmod9\)**
in some order. Precisely one of these
even-index states, say \(b_j\), therefore
has \(9\mid(2b_j+5)\). The actual t=1
source coordinate
\[
 w=\frac{2(2b_j+5)}9
\]
lies in the odd source band
\[
  3p/8+1\le w\le p/2-1,
\]
since \(7p/8<b_j\le p-3\) and
\(p\gg n\). Its odd predecessor
\[
 h_{\mathrm{odd}}=2w-p/2-(n-4)-5
\]
is nonnegative by \(p>4n\), so
this is a genuine t=1 ResetParent.
The separate even parent \(b_{j+1}\)
lies above \(3p/4-1\), whereas
\(h_{\mathrm{odd}}<p/2\), hence they
are distinct. Other higher-t parents
may exist but are irrelevant to this
**at-least-two-parent** conclusion.

A full BigInt evaluation of the
untruncated parent grammar for
n=7199, 28703, 28757 and 28811 found
the predicted fork at j=2,2,4,0
respectively. This is a finite diagnostic;
the uniform theorem is the modular cycle
plus the dyadic interval argument.

**Interpretation:** the low-valuation
sector that Section 5 can exclude
by a unique chain is genuinely different
from this sector. Every proof attempting
to close all terminal ancestor trees in
the narrow high-c strip must explicitly
resolve a **second-tier odd branch**
somewhere among \(b_0,b_2,b_4\).
Neither the existence nor the pruning of
such a synthetic odd fork establishes
reachability from the blank root.

## 9. A complete nonterminal inverse fork: two steps nearer the fatal gate

The preceding results resolve the deepest canonical-ray node
\(u_J\). We can do more: an infinite subfamily has a **complete
inverse cone for \(u_{J-2}\)**, incorporating an actual off-spine
odd predecessor. This is the first result here that closes a
genuine two-arm fork **above** the terminal node, not merely its
terminal path.

**Theorem (exact nonterminal four-node inverse cone, paper proof).**
For any surviving gate \(n\ge257\), n mod6∈{4,5}, put
\(p=2^n,\ c=2n+3,\ a=\lfloor\log_2 c\rfloor,\ J=n-a,\ q=c2^J\).
Assume \(J\) even, \(4c>7\cdot2^a\), and
\[
 X_-:=2u_{J-2}+5
       =8p+2n+3-q/2\equiv9\pmod{27}.
\]
Then the **entire** inverse ResetParent graph
of the nonterminal ray state \(v=u_{J-2}\) is
\[
 \begin{array}{ccccc}
  &&v&&\\[-2pt]
  &\swarrow&&\searrow&\\[-2pt]
  w=u_{J-1}&&&&h\\[-2pt]
  \downarrow&&&&\\[-2pt]
  z=u_J&&&&
 \end{array}
\]
with exact two parents \(w,h\) of \(v\), exact sole parent
\(z\) of \(w\), and **both \(h,z\) parentless**,
where
\[
 \begin{aligned}
  w&=4p+n-1-q/2,\\
  z&=4p+n-1-q,\\
  h&=4(X_-/9)-2p-n-3
     =(14p-2q-n-15)/9.
 \end{aligned}
\]
Neither terminal leaf is the blank root 2. Consequently,
\[
 \boxed{\neg\operatorname{ResetChain}(2,u_{J-2})},
 \qquad
 \boxed{\neg\operatorname{ReachC}((2,0),(u_{J-2},0))}.
\]
The source-reachability equivalence is previously certified;
the new infinite-parametric classification remains uncompiled.

**Proof: even edges and no extra even parents.**
The actual \(u_{J-2}\) and \(u_{J-1}\)
lie in the level-(n−1) even-target band
\([3p-1,4p-3]\). Their unique even parents
are respectively \(w\) and \(z\), by
\(2u_j=4p+(n-1)+u_{j+1}\).
The final \(z\) lies in the entire even-parent
gap \((2p,3p-1)\), as in Section 4.

**Proof: the only odd fork from v.**
The parity \(J-2\) is even, and \(X_-\bmod27=9\),
so \(v_3(X_-)=2\). For t=0, the would-be
source coordinate \(d_0=X_-/3\) lies
strictly inside \((2p,3p)\), the gap between
the odd source bands at levels n−2 and n−1;
there is no t=0 parent. For t≥2, output
divisibility would require \(27\mid X_-\),
contradicting its residue. The only remaining
valuation is t=1. Its source coordinate
\(2d=2X_-/9\) lies in
\([3p/2+1,2p-1]\), the odd-source
band at level n−2; its exact parent is
the above \(h\), which is positive.
Thus \(v\) has exactly the two displayed
parents, an even \(w\) and an odd t=1 \(h\).

**Proof: the off-spine h is an immediate leaf.**
Using \(7p/4<q<2p\) in its closed form,
\[
  p<h<3p/2-1.
\]
This is an open even-target image gap
at all dyadic scales. Since \(n\bmod6\in
\{4,5\}\), we have \(2p+n\equiv0\pmod3\).
Therefore
\[
  h\bmod3=(X_-/9)\bmod3=1,
\]
so \(3\nmid(2h+5)\) and no odd parent
exists at any valuation. This proves
that \(h\) is parentless.

**Proof: the on-spine w and z have no odd forks.**
Define \(X_w=2w+5=X_--q/2\).
The factor \(q/2=c2^{J-1}\) is coprime
to three (because \(c=2n+3\) is
1 or 2 modulo 3). Thus
\(X_w\not\equiv0\pmod3\), and
w has no odd parent. Finally
\[
  X_z=2z+5=X_--3q/2
       \equiv-3(q/2)\not\equiv0\pmod9,
\]
because \(9\mid X_-\) and \(3\nmid(q/2)\).
Since z is in the high-c terminal
even-target gap, Section 4 implies that
z has no odd or even parent. Hence
the exact four-node inverse tree closes.

This is a **true blank-root exclusion two ray
indices closer to the original gate**, but
still not the gate itself: other odd forks
leaving earlier even ray states can bypass v.

**Positive-density sector.** For each large
complete dyadic a-block, these n occupy
asymptotically
\[
 \frac12\cdot\frac14\cdot\frac19
   =\boxed{\frac1{72}}
\]
of the surviving original gate indices.
Indeed J even selects one gate residue
sector, high-c selects the last quarter
of the a-block, and the exact 3-adic
shift of \(X_-\) through its nine
mod-54 lifts selects one class with
\(X_-\bmod27=9\). The count refers to
the \(u_{J-2}\) inverse **branch**, not
to full fatal target nonreachability.

**Corollary (complete nine-node cone seven levels before termination).**
In the exact same parameter family, the whole inverse cone of
\(u_{J-7}\) is still finite and root-dead: it consists of the
eight-node canonical even chain
\[
  u_{J-7}\leftarrow u_{J-6}\leftarrow\cdots
          \leftarrow u_{J-1}\leftarrow u_J
\]
and **only one** additional odd leaf, attached at \(u_{J-2}\)
as above. Hence
\[
 \boxed{\neg\operatorname{ReachC}((2,0),(u_{J-7},0))}.
\]
To see there are no further off-spine forks in this segment,
note the exact signed identity
\(X_j=2u_j+5=8p+2n+3-2c\,2^j\).
For every even \(j\le J-2\), the possible t=0
source parameter \(X_j/3\) lies in the universal gap
\((2p,3p)\). Thus any odd parent must have t≥1
and hence require \(9\mid X_j\). Among even-index
depths, \(X_{j+2}-X_j=-6c\,2^j\) is congruent
to the same nonzero multiple of three modulo nine
(because \(c\not\equiv0\pmod3\)).
Consequently the three successive even depths
\(J-2,J-4,J-6\) have \(X_j\bmod9\) in
\(\{0,3,6\}\), exactly once each. Their only
9-divisible member is the already closed
\(j=J-2\) fork; all odd-index depths have
\(3\nmid X_j\). No further parent occurs
between \(u_{J-7}\) and the terminal state.

The extension is also **sharp for this simple argument**:
\(9\mid X_{J-8}\) again by the six-step modular
period, and its t=1 odd source lies in a genuine
scale-(n−2) band. Thus extending to
\(u_{J-8}\) requires a second off-spine fork
analysis (and possibly higher t). The corollary
moves the certified *paper-level* root-dead
segment seven inverse levels nearer the
original fatal target; it does not reach
\(U_n=u_0\).

A full untruncated BigInt ResetParent
enumerator tested 37 qualifying n≤10000,
including n=455,509,928,982,1817:
all 37 had precisely the four-node tree
above and zero unexpected parents.
That is a consistency check, not the
uniform proof.

## 10. Two complete off-spine forks: a 17-node inverse cone thirteen levels out

The exact nine-node cone in Section 9 can be extended across
the **next six-step Hensel period** in two explicit infinite
subfamilies. This resolves two distinct nonterminal odd forks,
not just a root-dead single spine.

**Theorem (complete depth-13 reverse cone; paper proof).**
Assume the Section 9 gate hypotheses \(n\ge257\),
\(n\bmod6\in\{4,5\}\), \(J\) even,
\(4c>7\cdot2^a\), and
\(X_{J-2}=2u_{J-2}+5\equiv9\pmod{27}\).
Write
\[
  X_8:=2u_{J-8}+5,\quad
  d_8=X_8/9,\quad
  h_8=4d_8-2p-n-3,\quad
  g_8=2h_8-2p-n+2.
\]
Suppose one of the following further modular alternatives:

\[
\begin{array}{ll}
{\rm (A)}&n\bmod6=4,\quad (2h_8+5)\bmod27\ne0;\\
{\rm (B)}&n\bmod6=5,\quad X_8\bmod81=54.
\end{array}
\]

Then the **full** inverse ResetParent cone of
\(u_{J-13}\) consists of **exactly 17 distinct
vertices**, namely the fourteen consecutive
canonical even-ray states
\(u_{J-13},u_{J-12},\ldots,u_J\),
the first off-spine odd feeder \(h_2\)
at \(u_{J-2}\) (defined in Section 9),
and the second fork
\[
   u_{J-8}\longleftarrow h_8
                     \longleftarrow g_8.
\]
The only leaves are \(u_J,h_2,g_8\).
All three differ from the blank root 2.
Therefore
\[
 \boxed{\neg\operatorname{ResetChain}(2,u_{J-13})}
 \quad\text{and}\quad
 \boxed{\neg\operatorname{ReachC}((2,0),(u_{J-13},0))}.
\]

**Proof: isolation of the next odd fork.**
By the six-step period of \(2^j\bmod9\),
\(j=J-8\) is the next even ray index,
going backward from \(J-2\), for which
\(9\mid X_j\). Every intermediate
\(j=J-3,\ldots,J-7\), and every
\(j=J-9,\ldots,J-13\), has no odd
parent: odd j gives \(3\nmid X_j\),
while the other even j have
\(9\nmid X_j\) and a t=0
source in the gap \((2p,3p)\).
Their only parent is the canonical
even successor. The earlier four-node
fork remains exactly as in Section 9.

At \(j=J-8\), the t=0 source is still
in the gap \((2p,3p)\). The t=1 odd
source \(2X_8/9\) lies in the
level-(n−2) band
\([3p/2+1,2p-1]\), producing the
displayed \(h_8\), in addition to the
canonical even parent \(u_{J-7}\).

The exact congruence
\[
  X_{J-2}-X_8
       =-126c\,2^{J-8}
\]
shows that \(X_8\bmod27=18\) in
sector \(n\bmod6=4\), and
\(X_8\bmod27=0\) in sector
\(n\bmod6=5\).
In (A) this gives \(v_3(X_8)=2\),
so no odd t≥2 parent of \(u_{J-8}\)
exists. In (B), \(v_3(X_8)=3\):
the only possible additional
valuation t=2 has source coordinate
\(4X_8/27\in(p,3p/2)\), an
odd-source gap, while t≥3 requires
\(81\mid X_8\), excluded by
\(X_8\bmod81=54\).
Thus in both alternatives the only
odd parent of \(u_{J-8}\) is \(h_8\).

**Proof: both levels of the new fork close.**
Using \(7p/4<q<2p\), the explicit
formula is
\[
 h_8=\frac{14p-q/32-n-15}{9},
\]
which lies in the \(k=n-2\) even-target
band \([3p/2-1,2p-3]\).
Its **only** even predecessor is
\[
 g_8
  =\frac{10p-q/16-11n-12}{9},
 \qquad p<g_8<9p/8-4,
\]
in the gap between even-target bands.
The elementary growth \(p\gg n\) for
n≥257 makes all endpoint inequalities
strict.

In case (A), \(h_8\bmod3=2\).
Its t=0 odd source \((2h_8+5)/3\)
lies in the odd-band gap \((p,3p/2)\);
its t=1 source \(2(2h_8+5)/9\),
when integral, lies in
\((p/2,3p/4)\), another gap.
Any t≥2 odd parent requires
\(27\mid(2h_8+5)\), excluded by
the (A) hypothesis. Hence
\(h_8\) has only the even parent
\(g_8\). The latter has
\(g_8\bmod3=0\), eliminating all
odd parents; its even-target gap
eliminates the rest. Thus \(g_8\)
is a nonroot leaf.

In case (B), \(h_8\bmod3=0\),
so it has no odd parent to begin
with. Its only parent is \(g_8\),
which has \(g_8\bmod3=2\).
The t=0 source of \(g_8\) lies
below the level-(n−3) lower
band, because \(g_8<9p/8-4\).
Write \(d_8=X_8/9\). From
\[
 2g_8+5=16d_8-12p-6n-3
\]
and \(d_8\bmod9=6\)
(the (B) residue), \(p\bmod9=5\)
and \(n\bmod3=2\), one gets
\[
 (2g_8+5)\bmod9=3.
\]
Thus every t≥1 odd parent is
impossible. Again \(g_8\) is
parentless and different from 2.
These cases exhaust the second fork;
the 17-node cone is complete.

**Asymptotic positive-density subfamilies.**
For fixed large even a, (A)
occupies asymptotically
\[
  \frac1{72}\cdot\frac89
  =\boxed{\frac1{81}}
\]
of surviving gate indices within
the full dyadic a-block. The extra
8/9 follows from the exact
shift \(n\mapsto n+54\):
once \(X_{J-2}\bmod27=9\)
is fixed, \((2h_8+5)\bmod27\)
cycles through the nine multiples
of three in a period-nine orbit.
In fact its step is 3, 12, or 21
mod27 according to \(a\bmod6\);
exactly one of nine lifts fails (A).

For fixed large odd a, (B)
occupies asymptotically
\[
 \frac1{72}\cdot\frac13
 =\boxed{\frac1{216}}
\]
of surviving gate indices.
On increments \(n\mapsto n+54\),
\(X_8\bmod81\) advances by 54
(derived using \(2^{54}\equiv1
\pmod{81}\) and \(J-7\) odd),
cycling through \(0,27,54\);
one of three lifts meets (B).
Both count estimates have \(O(2^{-a})\)
boundary errors. They measure
**the fully closed 13-level inverse
branch**, not all fatal gates.

The untruncated original ResetParent
BigInt enumerator checked 19 qualifying
indices n≤11000 (10 in case A, 9 in
case B). Every one had **exactly 17
vertices, three parentless leaves and
two genuine fork nodes**, with no
unexpected source-grammar parent.
These are finite checks of the
paper derivation; neither the
17-node theorem nor the densities
have yet been source-compiled in Lean.

## 11. Uniform nine-packet obstruction: an unavoidable genuine t=3 odd parent

The previous full-cone exclusions are necessarily finite-depth phenomena
for any strategy that refuses higher odd valuations. There is an exact
**all-index source-grammar obstruction**: every high-c terminal family
covered by Section 9 carries a *genuine third-valuation odd parent*
within nine successive active canonical-ray packets, not merely an
arithmetical divisibility witness.

**Theorem (forced triple source-parent fork; paper proof).**
Suppose n≥257, n mod6∈{4,5}, J=n−floor(log2(2n+3)) even,
\(q=(2n+3)2^J\), \(p=2^n\), \(4q>7p\), and
\[
     X_0:=2u_{J-2}+5\equiv9\pmod{27}.
\]
Put \(j_r=J-2-6r\) and \(X_r=2u_{j_r}+5\).
There is a **unique** \(r_*\in\{1,\dots,8\}\) with
\[
 \boxed{81\mid X_{r_*}}.
\]
Moreover \(u_{j_{r_*}}\) has **at least three distinct genuine
ResetParent predecessors**: its canonical even-ray parent,
a t=1 odd parent at scale \(k=n-2\), and a t=3 odd parent at
scale \(k=n-3\). Thus one cannot close the entire \(u_0\)
inverse tree on these parameter sectors using only even and
t=1 predecessors. This is a forced *branch existence*,
not a blank-root reachability claim.

**Proof of the unique valuation packet.** Define
\(A=8p+2n+3\) and \(Z_r=2(2n+3)2^{j_r}\),
so \(X_r=A-Z_r\).
The gate-sector restriction gives \(3\nmid(2n+3)\), hence
\(3\nmid Z_0\). As \(2^6=64\) and
\[
       64^{-1}\equiv19\equiv1+18\pmod{81},
\]
for r=0,…,8 we obtain
\[
  Z_r\equiv Z_0\cdot19^r
       \equiv Z_0(1+18r)\pmod{81},\qquad
  X_r\equiv X_0-18rZ_0\pmod{81}.
\]
Because \(3\nmid Z_0\), the increments \(-18Z_0\)
generate every multiple of nine modulo 81 **exactly once**
over r=0,…,8. Since \(9\mid X_0\), precisely one
\(X_r\) vanishes modulo81; since \(X_0\equiv9\pmod{27}\),
it cannot be r=0. For n≥257, \(J>50\), so every
indicated ray index is positive and the equalities
are legitimate, not negative-index formal manipulations.

**Proof that the extra source parent is real.** Since
\(r_*\ge1\), \(j_{r_*}\le J-8\). Write \(j=j_{r_*}\),
\(X=X_{r_*}\), and \(d_1=X/9\), \(d_3=X/81\), both
positive odd integers. The small ray deficit
\(c2^j\le q/256<p/128\) gives
\[
   8p-p/64<X<8p+2n+3.
\]
Using n≥257 and \(p=2^n\gg n\), these explicit
inequalities imply
\[
  6\cdot2^{n-2}+1\le2d_1\le8\cdot2^{n-2}-1,
\]
\[
  6\cdot2^{n-3}+1\le8d_3\le8\cdot2^{n-3}-1.
\]
Therefore the t=1 and t=3 odd arms of the
**original untruncated** ResetParent grammar
are both valid. The corresponding source-parent
numbers are exactly
\[
 h_1=4d_1-2p-n-3,\qquad
 h_3=16d_3-p-n-2.
\]
Both are nonnegative, and the same bounds give
\[
  p<h_1<2p,\qquad p/2<h_3<p.
\]
Meanwhile the canonical even predecessor
\(u_{j+1}>3p\), so all three source parents
are pairwise distinct.

**Higher 3-adic hierarchy.** The same mechanism repeats
at powers \(3^k\): the exact lifting formula
\(\nu_3(2^{6m}-1)=2+\nu_3(m)\) shows that
\(2^6\) has order \(3^{k-2}\) modulo \(3^k\)
for \(k\ge2\). Conditional on the active
\(9\mid X_r\) phase, each complete block of
\(3^{k-2}\) active packet indices contains
precisely one \(r\) with \(3^k\mid X_r\), provided
all those dyadic ray indices exist. Thus
arbitrarily high odd-output valuations are
structurally **forced as n grows**. Which
valuations produce *genuine* odd-source bands
depends on \(2^{t+1}/3^{t+1}\) and the disjoint
dyadic band geometry; t=3 above is the
first unavoidable genuinely additional odd
source after t=1.

**Reproduction.** An independent exact BigInt
calculation for n=455,509,928,982,1817,
1871,1925,2033,3616,3778 found exactly one
r in 1,…,8 with X_r%81=0 in every case,
and checked the actual odd source bands, both
parent nonnegativity conditions and all three
pairwise distinct parents. This finite check is
not used to justify the all-index modular proof.

**Research implication.** A sustainable path to
closing the full original #746 gate inverse
tree must address the forced high-valuation
t=3 branches (and eventually the higher
3-adic hierarchy), instead of endlessly
expanding t=1-only residue cylinders.
The source-connected Lean certification of
this all-index nine-packet theorem remains
an open formalization task.

## 12. Universal forced t=3 triple branch in EVERY surviving gate's first 54 ray states

The nine-packet theorem above was conditioned on one high-c
terminal phase. The source phenomenon is in fact **unconditional
over all surviving original #746 halting-gate indices**:
every one contains a genuine third-valuation odd fork
near the *original fatal target*, not only near the
terminal inverse ray.

**Theorem (all-index genuine three-parent obstruction; paper proof).**
For every \(n\ge257\) with \(n\bmod6\in\{4,5\}\), write
\[
 p=2^n,\quad c=2n+3,\quad
 a=\lfloor\log_2 c\rfloor,\quad J=n-a,\quad
 u_j=4p+n-1-c\,2^j.
\]
There exists **exactly one even** index
\(j_*(n)\in\{0,2,4,\ldots,52\}\) with
\[
 \boxed{81\mid 2u_{j_*}+5.}
\]
There are no odd indices j in 0,…,53
satisfying the divisibility.
Moreover, at \(u_{j_*}\) the exact
original \(\mathrm{ResetParent}\) grammar
has **at least three pairwise distinct
genuine parents**:
\[
 \begin{aligned}
  E&=u_{j_*+1}
      &&\text{(even predecessor at scale n−1)},\\
  H_1&=4\,\frac{2u_{j_*}+5}{9}-2p-n-3
      &&\text{(odd valuation t=1 at scale n−2)},\\
  H_3&=16\,\frac{2u_{j_*}+5}{81}-p-n-2
      &&\text{(odd valuation t=3 at scale n−3)}.
 \end{aligned}
\]
Their locations satisfy
\[
  p/2<H_3<p<H_1<2p<3p<E.
\]
In particular **no argument treating only the
even and first odd (t=1) parent can
close the full source inverse tree of
*any* surviving gate**. This is a
necessary-branch theorem, not a
blank-root accessibility or halting result.

**Uniform modular existence and uniqueness.** Put
\(A=8p+2n+3\); then
\[
     2u_j+5=A-2c\,2^j.
\]
For n mod6=4, \(p\equiv n\equiv1\pmod3\),
\(A\equiv2c\equiv1\pmod3\);
for n mod6=5, \(p\equiv n\equiv2\pmod3\),
\(A\equiv2c\equiv2\pmod3\).
Thus \(A/(2c)\) is a well-defined
unit modulo81 congruent to 1 modulo3.

The element 4 has **exact order 27**
modulo81: \(4^{27}\equiv1\pmod{81}\)
and \(4^9\equiv28\not\equiv1\pmod{81}\).
Its 27 powers therefore enumerate
*exactly* the 27 units congruent to 1
modulo3. Consequently there is a
unique \(r\in\{0,\ldots,26\}\) with
\[
 4^r\equiv A(2c)^{-1}\pmod{81}.
\]
Taking \(j_*=2r\) gives
\(81\mid A-2c\,2^{j_*}\).
No odd j can solve this congruence
because then \(2^j\equiv2\pmod3\),
whereas \(A/(2c)\equiv1\pmod3\).
This proves the exact index assertion.

**The third odd source really exists.**
The elementary growth bound
\(2n+3<2^{n-61}\) for n≥257
implies \(J\ge62\), so
\(j_*\le52\le J-8\).
Hence the ray deficit satisfies
\[
 c2^{j_*}\le c2^{J-8}
     =q/256<p/128,\quad q=c2^J<2p,
\]
and therefore, with
\(X=2u_{j_*}+5\),
\[
  (8-1/64)p<X<8p+2n+3.
\]
Since \(81\mid X\) and X is odd,
\(d_3=X/81\) and \(d_1=X/9\)
are positive odd integers.
The bounds imply the exact
odd-source intervals
\[
 \begin{aligned}
   6\cdot2^{n-2}+1&\le 2d_1
                            \le8\cdot2^{n-2}-1,\\
   6\cdot2^{n-3}+1&\le 8d_3
                            \le8\cdot2^{n-3}-1.
 \end{aligned}
\]
For n≥257 all three displayed
parent coordinates are nonnegative,
and the even-target band at
\(u_{j_*}\) contains the canonical
parent \(E\). Their disjoint
\(p\)-scale intervals establish
pairwise distinctness. This verifies
every required inequality and output
equation in the *source* odd grammar;
divisibility alone was not taken
as evidence of a parent.

**Simple periodicity and reproducibility.**
Both \(n\bmod81\) and
\(2^n\bmod81\) repeat after
\(n\mapsto n+162\) (because the
order of 2 modulo81 is 54),
so the unique ray index \(j_*(n)\)
is **162-periodic** along the
eligible n sectors. An independent
exact-integer census over all
981 eligible n from 257 through
3200 found exactly one such
even index j≤52 each time and
verified *all* original source
bands, positivity, and parent
separation. The all-parameter
proof is the primitive-root and
interval argument, not that
finite census.

**Practical consequence.** Attempts
to prove original #746 never halts
must explicitly close t=3 inverse
forks, even for arbitrarily large n
and even *within the first 54
canonical inverse levels of the
actual fatal target*. This is
stronger than the conditional
nine-packet obstruction of Section11.
A separate Lean source theorem
[ForcedThirdValuationSource.lean](ForcedThirdValuationSource.lean)
proves genuine t=3 parent existence
under the uniform band inequalities,
while the all-index modular
selection remains a paper proof
pending Lean integration.

A further [uniform all-gate ray-fanin theorem](EveryGateRayFanin.md) strengthens this fixed-t=3 phenomenon: for every m and all n≥100·3^(3m+1) in either surviving gate sector, some interior even ray vertex has at least m+1 genuine distinct ResetParent predecessors. The proof uses this same primitive-root selector at arbitrary ternary precision and Agent44's already source-checked every-three-odd-valuation lemma. It remains a paper-level modular/source composition and does not decide rooted reachability.

A separate [all-index parentless third-valuation packet theorem](ThirdForkPacketLeaves.md) now combines the source-accepted `depthResidue_iff` and `ray_tthree_parent_gap` with a paper-level modulo-243 three-lift argument: for every n≥257 in either gate sector, **each complete 162-index period** in the physical high-margin prefix has exactly three genuine t=3 odd parents and **two of these offray parents have no ResetParent** (not just no blank-root path). This yields ≥2⌊(J−13)/162⌋ distinct source-parentless t=3 feeders along every gate's canonical ray. It remains an intermediate universal source-graph pruning result, not a gate decision.

## 13. Where the current E-parent results apply

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

## 14. Existing Ray reductions to compose, not duplicate

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

## 15. Scope and remaining work

This identity connects the auxiliary entry family to the actual #746 halting targets. It proves that (E(a,K)) is an ancestor on **one** inverse-parent branch of (U_{K+2}). It does **not** prove that every root path to (U_{K+2}) passes through (E(a,K)). Other odd-parent side branches can leave intermediate spine nodes; a root path could in principle enter through one of them.

The following are still required for a global #746 conclusion:

1. Formalize the chain identity, terminal predecessor criterion, full unique-chain exclusion, and two-edge exclusion against the exact `ResetParent` and `ResetChain` definitions in Lean.
2. Compose the existing Ray reductions listed above with every (t\ge1) side branch leaving the intermediate (u_j), and prove the hypotheses exhaust the full spine (or identify the uncovered cases).
3. Extend the E-parent exclusions beyond the current narrow x-window and across the remaining parity/phase sectors.
4. Combine the branch classifications with `OriginalAlgorithmicGate.lean` to exclude every (n\ge257) with (n\bmod6\in\{4,5\}).

Exact BigInt checks were made for representative pairs including ((K,a)=(387,9)) and ((800,10)), yielding the predicted (J+1)-edge chain. These are consistency checks only; the algebraic derivation above is the substantive claim, and the Lean formalization is pending. No #746 nonhalting or BB(6) conclusion is claimed.
