# Wider residue-cut exclusion for the second-level Space Needle parent

**Status:** new paper-level arithmetic theorem with an exact BigInt audit. It has not yet been Lean-formalized or checked against the pinned original-source inverse theorem. This is an intermediate result, not a BB(6) decision.

## 1. Setup and theorem

Let
\[
r=110j+50,\quad j\in\mathbb N,\qquad
a=\frac{9^r+5}{2},\quad A=2^a,
\]
and define
\[
P_0(A)=0,\qquad P_{m+1}(A)=A^2P_m(A)+9^m(A-3).
\]
For this progression the second-level target \(y\) is an integer satisfying
\[
55y=8AP_r(A)+25.
\]
Put
\[
n=3^{2r-1},\qquad d=1+\lfloor\log_2 n\rfloor.
\]
The standard odd-gap argument gives
\[
2^d\ge n+5. \tag{1}
\]
Indeed, \(2^d-n\) is positive and odd; it cannot be \(1\), since \(3^{2r-1}+1\) has an odd factor greater than \(1\), and it cannot be \(3\), since \(n+3\) is divisible by \(3\).

For \(s\ge1\), set
\[
c(s)=((a+s-5)\bmod s)+1,
\]
so \(1\le c(s)\le s\). Consider a possible immediate parent of \(y\) at valuation
\[
w=a+s-1.
\]
Its exact parent equation is
\[
y=(2^{a+s}+3)q+3\cdot2^{a+s-1}+a+s+2,\qquad q\in\mathbb N. \tag{2}
\]

**Theorem.** For every \(r=110j+50\), no \(q\in\mathbb N\) satisfies (2) whenever
\[
\boxed{
(2r-1)s\ge a,\qquad
(r-1)s\le a-d-3,\qquad
c(s)\ge d.
} \tag{3}
\]
Equivalently, the theorem excludes all valuations \(w=a+s-1\) in the interval
\[
\left\lceil\frac a{2r-1}\right\rceil
\le s\le
\left\lfloor\frac{a-d-3}{r-1}\right\rfloor
\]
except for the explicitly enumerable residue-cut exceptions \(c(s)<d\).

The interval is extremely large. Nevertheless, at most
\[
\boxed{r(d-1)}
\]
values of \(s\) in it fail the residue condition \(c(s)\ge d\).

## 2. Proof

Write
\[
t=2^s,\quad S=\sum_{i=0}^{2r-1}t^i,\quad
D=2^{a+s}+3,\quad
C=55\cdot9^r+110s-50.
\]
Equation (2) implies \(D\mid 2y-2w+3\). Multiplying by \(55\), using \(55y=8AP_r(A)+25\), and substituting \(w=a+s-1\), gives
\[
D\mid16AP_r(A)-C. \tag{4}
\]

The recurrence for \(P_r\) gives
\[
AP_r(A)=\sum_{i=0}^{2r-1}(-3)^iA^{2r-i}.
\]
Since \(At=2^{a+s}\equiv-3\pmod D\), multiplying this identity by \(t^{2r}\) yields
\[
t^{2r}AP_r(A)\equiv3^{2r}S\pmod D.
\]
Thus (4) implies
\[
D\mid Q,\qquad Q:=Ct^{2r}-48nS. \tag{5}
\]
Here \(C>48n\), \(S<t^{2r}\), and hence \(Q>0\). Also \(16\mid Q\), because \(s\ge1\) and \(r\ge2\). Since \(D\) is odd, writing \(Q=Dz\) gives \(z=16z_1\) for a positive integer \(z_1\). Dividing by \(16\),
\[
Dz_1=C2^{2rs-4}-3nS. \tag{6}
\]

Set
\[
M=2^{a+s-4}.
\]
The first condition in (3) gives \(2rs-4\ge a+s-4\), so \(M\mid2^{2rs-4}\). As \(D=2^{a+s}+3\equiv3\pmod M\), reducing (6) modulo \(M\) gives
\[
M\mid3(z_1+nS).
\]
Since \(M\) is a power of two,
\[
M\mid z_1+nS. \tag{7}
\]

Now define
\[
L=\left\lfloor\frac{a+s-5}{s}\right\rfloor,
\qquad c=c(s).
\]
Then
\[
Ls+c=a+s-4,\qquad 1\le c\le s.
\]
The first condition in (3) also gives \(L+1\le2r\), and \(M\mid t^{L+1}\). Splitting the geometric sum at \(L\), (7) becomes
\[
M\mid z_1+R,\qquad
R:=n\sum_{i=0}^{L}t^i. \tag{8}
\]

We next bound the two positive terms in (8). Since \(c\ge d\), (1) gives \(t\ge n+5\) and
\[
2^c\ge2^{d+(c-d)}\ge2^{c-d}(n+5).
\]
The finite geometric-sum identity therefore gives
\[
n\sum_{i=0}^{L}t^i<(n+1)t^L
\le(2^c-2^{c-d+2})t^L.
\]
Writing \(h=c-d\), and using \(Ls+c=a+s-4\), this is
\[
R<M-2^{h+2}t^L. \tag{9}
\]

For the other term, (5) and \(D>2^{a+s}\) imply
\[
z_1=\frac{Q}{16D}
< C\,2^{2rs-a-s-4}
= C\,2^{-E}t^L,
\qquad
E:=2a-(2r-2)s-c. \tag{10}
\]
The second condition in (3) is equivalent to
\[
E+c=2a-(2r-2)s\ge2d+6.
\]
Thus \(E+h+2\ge d+8\), and (1) gives
\[
2^{E+h+2}\ge2^{d+8}\ge256(n+5). \tag{11}
\]

It remains to bound \(C\). The second condition in (3) implies
\[
s\le\frac{a-d-3}{r-1}<\frac a{r-1}\le\frac a2
\]
because \(r\ge3\). Since \(9^r=3n\) and \(a=(3n+5)/2\),
\[
C=165n+110s-50
<165n+55a
=\frac{495n+275}{2}
<256(n+5). \tag{12}
\]
Combining (11) and (12), \(C<2^{E+h+2}\). Equation (10) consequently gives
\[
z_1<2^{h+2}t^L. \tag{13}
\]
Equations (9) and (13) show
\[
0<z_1+R<M.
\]
This contradicts \(M\mid z_1+R\) in (8), proving the theorem. \(\square\)

## 3. Why only finitely many residue-cut exceptions remain

Inside the interval in (3), suppose \(c(s)<d\). Write
\[
e=c(s)-1=((a-5)\bmod s),\qquad 0\le e\le d-2.
\]
Then
\[
a-5=ks+e,\qquad k=\left\lfloor\frac{a-5}{s}\right\rfloor.
\]
The interval bounds imply
\[
r-1\le k\le2r-2.
\]
For the lower bound, \((r-1)s\le a-d-3<a-5\). For the upper bound, \(s\ge a/(2r-1)\), so \((a-5)/s<2r-1\). There are \(r\) possible \(k\)'s and \(d-1\) possible \(e\)'s. Each pair determines at most one
\[
s=\frac{a-5-e}{k}.
\]
Therefore there are at most \(r(d-1)\) exceptions. This is an explicit finite parametrization, not an asymptotic density estimate.

## 4. Exact finite audit

The accompanying second_level_wide_residue_cut.js enumerates only the exceptional pairs \((k,e)\), using BigInt arithmetic. It then applies the existing eleven-prime parent filters directly by computing \(y\bmod p\) from the recurrence modulo \(55p\), and applies the existing two-step conditions for \(t=1,\ldots,7\). No floating-point arithmetic or precomputed residue table is used.

| \(r\) | \(d\) | Bound \(r(d-1)\) | Exact exceptions | After eleven-prime filter | Forced-even survivors | Forced-even with \(t\le7\) | Forced-even requiring \(t\ge8\) |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 50 | 157 | 7,800 | 105 | 41 | 28 | 7 | 21 |
| 160 | 506 | 80,800 | 346 | 121 | 105 | 37 | 68 |

The odd-entry branch is separately classified by the existing mod-5/mod-25 odd-block results. For \(r=50\), the 41 prime survivors contain 13 odd-entry cases: 2 are in the long-odd-block families, while 11 are short-block cases, of which 6 require the next even valuation to be at least 8. For \(r=160\), there are 16 odd-entry cases: 3 long-block and 13 short-block, with 8 short-block cases requiring the next even valuation to be at least 8.

These are necessary-condition audits. A candidate passing a filter is not thereby shown to have a parent or to be reachable. A candidate failing every tested \(t\le7\) condition can only continue through a larger valuation (or, in the separately identified long odd-block cases, through the remaining odd-block analysis).

## 5. Scope and next mathematical obligation

This theorem materially extends the existing high-side exclusion for the second-level target: it removes a wide interval of valuations just above \(a\), leaving only \(O(r^2)\) explicit residue-cut candidates for each fixed \(r\). The exact audit further reduces those candidates.

It does **not** close the remaining \(w<a\) middle-remainder quotient classes in SecondLevelParentSieve.md, prove the remaining candidates unreachable, establish Space Needle nonhalting, or determine BB(6). The next useful attack is to combine the finite exception parametrization with stronger even-parent constraints for \(t\ge8\), while separately treating the few long odd-block cases. The theorem and audit belong in im-results/, not results/, until formalization and source integration are complete.

Related work:
- im-results/agent20-needle-coprime/SecondLevelParentSieve.md
- im-results/agent20-needle-coprime/SecondLevelOddBlockFilter.md
- im-results/agent46-needle-two-step/README.md
- im-results/agent46-needle-two-step/two_step_even_parent_audit.js
