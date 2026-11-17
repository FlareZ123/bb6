# Cancellation-feeder valuation bands around the first two powers of A

**Status:** intermediate arithmetic proof draft, not Lean-compiled in this invocation. It is not a blank-root reachability theorem.

Let
\[
a_r=(9^r+5)/2,\quad A_r=2^{a_r},\quad
P_r(X)=\sum_{j=0}^{2r-1}(-3)^jX^{2r-1-j},
\]
and define the exact one-parent necessary condition
\[
D_u:=2^{u+1}+3 \mid N_r(u):=A_rP_r(A_r)+3-2u.
\]
The polynomial satisfies the recurrence used in the existing cancellation-feeder dossier. A valuation \(u\) satisfying this divisibility is only a *synthetic immediate parent candidate*; it does not establish blank-root reachability.

This note records two arithmetic reductions: a sharpened central band around \(u=a_r-1\), and a second band around \(u=2a_r-1\). The first uses the existing all-\(r\) middle-band theorem of Agent 46; the second is a separate quadratic-elimination argument.

## 1. A lower-threshold-free band around \(a_r-1\)

Write
\[
d_r=1+\lfloor\log_2(3^{2r-1})\rfloor,\quad
T_{1,r}=\left\lfloor\frac{a_r-4r-3}{2r+1}\right\rfloor,\quad
S_{1,r}=\left\lfloor\frac{a_r-d_r}{2r-2}\right\rfloor.
\]
For every \(r\ge2\), the combined exclusion is
\[
\boxed{a_r-1-T_{1,r}\le u\le a_r-1+S_{1,r}
\quad\Longrightarrow\quad D_u\nmid N_r(u).}
\]

### Below \(a_r-1\)

Put \(u=a-1-t\), \(D=2^{a-t}+3\), where \(0\le t\le T_{1,r}\). Since \(2^{a-t}\equiv-3\pmod D\), we have \(A\equiv-3\cdot2^t\pmod D\). The recurrence gives
\[
P_r(-3\cdot2^t)=-3^{2r-1}\sum_{j=0}^{2r-1}2^{jt}.
\]
Using \(2a=9^r+5\), the numerator has residue
\[
N_r(a-1-t)\equiv
R_t:=3^{2r}\left(\sum_{j=1}^{2r}2^{jt}-1\right)+2t
\pmod D.
\]
For \(t=0\), the recurrence separately gives \(P_r(-3)=-2r\,3^{2r-1}\), hence
\[
R_0=(2r-1)3^{2r}.
\]
For \(t\ge1\), the geometric sum is \(<2^{2rt+1}\), so
\[
0<R_t<3^{2r}2^{2rt+1}+2t<2^{4r+2rt+2}.
\]
The threshold condition \((2r+1)t\le a-4r-3\) implies
\[
a-t\ge4r+2rt+3,
\]
and therefore \(R_t<2^{a-t-1}<D\). For \(t=0\), \((2r-1)3^{2r}<2^{8r}<2^a<D\), using \(a\ge8r+1\). Thus the displayed positive residue is strictly smaller than \(D\) throughout the lower interval.

### At and just above \(a_r-1\)

At \(s=0\), set \(u=a-1\) and \(D=A+3\). The recurrence gives
\[
P_r(-3)=-2r\,3^{2r-1},\qquad
N_r(a-1)\equiv(2r-1)3^{2r}\pmod{A+3}.
\]
For \(r\ge2\), \(0<(2r-1)3^{2r}<2^{8r}<2^a<A+3\).

For \(1\le s<d_r\), put \(u=a-1+s\), \(D=2^{a+s}+3\), and
\[
S=\sum_{j=0}^{2r-1}2^{js},\qquad
Q=(3^{2r}+2s)2^{2rs}-3^{2r}S.
\]
The exact polynomial reduction used in the existing middle-band proof gives \(D\mid N_r(u)\Rightarrow D\mid Q\). Since \(s\ge1\), \(0<Q<(3^{2r}+2s)2^{2rs}\). The elementary bounds \(d_r\le4r-3\) and \(9^r\ge16r^2\) imply
\[
a-(2r-1)s\ge12r-1,\qquad
3^{2r}+2s<2^{4r+1}\le2^{12r-1}.
\]
Consequently \(Q<2^{a+s}<D\), a contradiction.

For \(d_r\le s\le S_{1,r}\), use Agent 46's source-equation middle-band theorem. The premise \((2r-2)s\le a-d_r\) is automatic for \(0\le s<d_r\) from the already-proved \((2r-1)d_r\le a\), so the three cases join into the boxed interval.

## 2. A second band around \(2a_r-1\)

Define
\[
T_{2,r}^{-}=\left\lfloor\frac{2a_r-8r-8}{2r+1}\right\rfloor,\qquad
T_{2,r}^{+}=\left\lfloor\frac{2a_r-8r-6}{2r-1}\right\rfloor.
\]
For every \(r\ge2\),
\[
\boxed{2a_r-1-T_{2,r}^{-}\le u\le2a_r-1+T_{2,r}^{+}
\quad\Longrightarrow\quad D_u\nmid N_r(u).}
\]

The proof uses a quadratic elimination. Write
\[
g(X)=XP_r(X)+3-2u=E(X^2)-XO(X^2)+C,
\]
where
\[
E(Y)=\sum_{\ell=1}^{r}3^{2r-2\ell}Y^\ell,\qquad
O(Y)=\sum_{\ell=0}^{r-1}3^{2r-2\ell-1}Y^\ell,\qquad C=3-2u.
\]
If \(D_u\mid g(A)\) and a quadratic relation \(f(A)\equiv0\pmod{D_u}\) holds, then squaring \(A\,O(A^2)\equiv E(A^2)+C\pmod{D_u}\) eliminates \(A\). In each side of the band this produces a positive integer \(H\) divisible by \(D_u\), but strictly smaller than \(D_u\).

### Upper side: \(u=2a-1+s\)

Here \(D=2^{2a+s}+3\), so \(2^sA^2\equiv-3\pmod D\). Define
\[
\begin{aligned}
\bar E&=C2^{rs}+
  \sum_{\ell=1}^{r}(-1)^\ell3^{2r-\ell}2^{(r-\ell)s},\\
\bar O&=\sum_{\ell=0}^{r-1}(-1)^\ell3^{2r-\ell-1}2^{(r-1-\ell)s}.
\end{aligned}
\]
The squared congruence, after clearing the powers of \(2\), gives
\[
D\mid H^+:=\bar E^2+3\cdot2^s\bar O^2.
\]
For \(0\le s\le T_{2,r}^{+}\), we have \(s\le a\), hence
\[
|C|=4a+2s-5<4\cdot9^r.
\]
The terms in each alternating sum decrease in magnitude by a factor at most \(1/3\), giving
\[
|\bar E|<5\cdot9^r2^{rs},\qquad
|\bar O|<\tfrac12\,9^r2^{(r-1)s}.
\]
Thus
\[
0<H^+<26\cdot9^{2r}2^{2rs}
<2^{8r+5+2rs}\le2^{2a+s-1}<D.
\]
The strict positivity follows from \(\bar O\ne0\).

### Lower side: \(u=2a-1-t\)

Here \(D=2^{2a-t}+3\), so \(A^2\equiv-3\cdot2^t\pmod D\). Put
\[
E_t=\sum_{\ell=1}^{r}(-1)^\ell3^{2r-\ell}2^{\ell t},\qquad
O_t=\sum_{\ell=0}^{r-1}(-1)^\ell3^{2r-\ell-1}2^{\ell t}.
\]
The same squared congruence gives
\[
D\mid H^-:=(E_t+C)^2+3\cdot2^tO_t^2.
\]
For \(0\le t\le T_{2,r}^{-}\), we have \(t\le a\), so \(|C|=4a-2t-5<3\cdot9^r\). The terms of E_t and O_t are geometric in magnitude with ratio \(2^t/3\). For \(t=0,1\) the first term dominates; for \(t\ge2\) the last term dominates. In all cases, the geometric-tail bounds give
\[
|E_t|<4\cdot9^r2^{rt},\qquad
|O_t|<4\cdot9^r2^{(r-1)t}.
\]
Together with \(|C|<3\cdot9^r\), this yields \(|E_t+C|<7\cdot9^r2^{rt}\), and hence
\[
0<H^-<97\cdot9^{2r}2^{2rt}
<2^{8r+7+2rt}\le2^{2a-t-1}<D.
\]
Again \(O_t\ne0\): for \(t=0,1\) its first term strictly dominates the tail, while for \(t\ge2\) its final term does. This proves the lower side.

### Sample interval endpoints

These are arithmetic consequences of the formulas, not independent proof evidence.

| \(r\) | \(a_r\) | central \(k=1\) band | \(k=2\) band |
|---:|---:|---:|---:|
| 2 | 43 | [36, 61] | [73, 106] |
| 3 | 367 | [316, 455] | [633, 873] |
| 4 | 3283 | [2920, 3827] | [5840, 7497] |
| 5 | 29527 | [26844, 33215] | [53689, 65609] |
| 6 | 265723 | [245284, 292292] | [490569, 579753] |

Exact integer spot checks for \(r=2,3,4\) found no divisible indices in these intervals. The proofs above are the claimed basis; the spot checks are only sanity checks.

## 3. Root-facing scope and limitations

The bands eliminate two broad sets of **synthetic immediate-parent valuations** for every \(r\ge2\). They can be used as filters in the exact parent enumeration from NeedleGeneralInverseSource.lean.

They do **not** prove that a cancellation feeder is unreachable from the blank root. In particular, the known valuation-2 and valuation-4 synthetic parent families lie far below these bands, and all other valuations outside the bands remain to be classified. A complete root decision still requires the full reverse tree to be shown disjoint from the genuine start, or a separate history-sensitive invariant of the authentic orbit.

No theorem in this file has been Lean-compiled or imported against the unchanged source machine in this invocation. Keep it in im-results until the arithmetic lemmas, exact parent bridge, and transitive axiom profile are checked.
