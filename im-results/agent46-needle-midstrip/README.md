# Space Needle cancellation feeder: an all-r middle-band parent exclusion

**Status:** complete paper derivation; not yet Lean-compiled or independently source-audited in this incarnation. All arithmetic is exact.

## Result

Let
\[
a_r=\frac{9^r+5}{2},\qquad v_r=a_r-1=\frac{9^r+3}{2},\qquad
A_r=2^{a_r}.
\]
Let \(P_r(A)\) be the cancellation polynomial
\[
P_0(A)=0,\qquad P_{r+1}(A)=A^2P_r(A)+9^r(A-3),
\]
and put
\[
q_r=\frac{P_r(A_r)-3}{2},\qquad
X_r=2^{v_r}(2q_r+3)=2^{a_r-1}P_r(A_r).
\]
These are the shifted counters \(d+2\) of the synthetic cancellation feeders already constructed in im-results/agent20-needle-coprime/CancellationTerminalConstructive.lean. Their terminal exponent satisfies \(K_r+1=2ra_r\).

Define
\[
c_r:=2+\left\lfloor\log_2(3^{2r-1})\right\rfloor.
\]
For a possible immediate predecessor with valuation \(u=v_r+s\), the exact inverse equation is
\[
X_r=(2^{u+1}+3)q'+3\cdot2^u+u+3
\]
for some \(q'\in\mathbb N\). Multiplying by two shows that this requires
\[
D_{r,s}:=2^{a_r+s}+3
\quad\mid\quad
N_{r,s}:=A_rP_r(A_r)+3-2(v_r+s).
\]

**Theorem.** For every \(r\ge2\), no such predecessor exists whenever
\[
\boxed{\quad c_r\le s,\qquad (2r-2)s\le a_r-c_r.\quad}
\]
Equivalently, the entire integer interval
\[
v_r+c_r\ \le u\le\
v_r+\left\lfloor\frac{a_r-c_r}{2r-2}\right\rfloor
\]
is excluded from the inverse-parent valuation set.

This interval is nonempty for every \(r\ge2\). We have \(3^{2r-1}<2^{4r-3}\), by induction from \(27<32\), hence \(c_r\le4r-2\). Also \(9^r\ge16r^2\) for \(r\ge2\), by induction from \(81\ge64\), so \(a_r\ge8r^2+5/2\). Consequently
\[
a_r\ge(2r-1)(4r-2)\ge(2r-1)c_r,
\]
which is exactly the nonemptiness condition.

## Proof

Fix \(r\ge2\), abbreviate \(a=a_r\), \(v=a-1\), \(A=2^a\), and \(s\) in the stated range. Write
\[
S=\sum_{j=0}^{2r-1}2^{js},\qquad
D=2^{a+s}+3,\qquad
N=AP_r(A)+3-2u,\qquad u=v+s.
\]

The recurrence for \(P_r\) gives the exact polynomial identity
\[
P_r(A)=\sum_{j=0}^{2r-1}(-3)^jA^{2r-1-j}.
\]
Set \(B=A2^s\), so \(D=B+3\). Multiplying the polynomial identity by \(A2^{2rs}\), and using \(B\equiv-3\pmod D\), gives
\[
2^{2rs}AP_r(A)
=\sum_{j=0}^{2r-1}(-3)^jB^{2r-j}2^{js}
\equiv 3^{2r}S\pmod D.
\]
Consequently, if \(D\mid N\), then
\[
D\mid F,\qquad
F:=3^{2r}S-(2u-3)2^{2rs}.
\tag{1}
\]

Since
\[
2u-3=2(a-1+s)-3=9^r+2s=3^{2r}+2s
\]
and \(S<2^{2rs}\), we have \(F<0\). Put
\[
Q=-F=(2u-3)2^{2rs}-3^{2r}S>0,\qquad
z=Q/D,\qquad R=3^{2r-1}S.
\]
Under the assumption \(D\mid F\), \(z\) is a positive integer.

Let
\[
M=2^{\min(a+s,\,2rs)}.
\]
Both \(2^{a+s}\) and \(2^{2rs}\) are divisible by \(M\). Thus \(D\equiv3\pmod M\), and \(Q\equiv-3^{2r}S\pmod M\). From \(Q=Dz\) it follows that
\[
M\mid 3(z+R).
\]
As \(M\) is a power of two, it is coprime to \(3\); hence
\[
M\mid z+R.
\tag{2}
\]
We prove \(0<z+R<M\), contradicting (2).

We use the elementary inequalities, valid for \(r\ge2\),
\[
2u-3=3^{2r}+2s\le3^{2r}+2a=2\cdot3^{2r}+5<2^{4r}
\tag{3}
\]
whenever \(s\le a\), and
\[
1+2\cdot3^{2r-1}<2^{c_r}.
\tag{4}
\]
For (3), \(a\ge4r+3\), so \(2^a\ge2^{4r+3}=8\cdot16^r>2\cdot9^r+5\), and in particular \(2^{4r}>2\cdot9^r+5\). For (4), write \(m=\lfloor\log_2(3^{2r-1})\rfloor\); then \(3^{2r-1}<2^{m+1}\), so \(1+2\cdot3^{2r-1}<2^{m+2}=2^{c_r}\).

We split according to which exponent defines \(M\).

### Case 1: \((2r-1)s\le a\)

Here \(M=2^{2rs}\), and \(s\le a\). Since \(D>M\),
\[
\frac zM=\frac{Q}{DM}<\frac{Q}{M^2}
<\frac{2u-3}{2^{2rs}}.
\]
The lower bound \(s\ge c_r\) gives \(2^{s-1}>3^{2r-1}\), so
\[
\frac RM<3^{2r-1}2^{1-s}<1.
\]
More precisely,
\[
1-\frac RM>
1-\frac{3^{2r-1}}{2^{s-1}}
\ge\frac1{2^{s-1}}.
\tag{5}
\]
We claim
\[
2u-3<2^{(2r-1)s+1}.
\tag{6}
\]
Indeed \(s\le a\), so \(2u-3=3^{2r}+2s\le2\cdot3^{2r}+5\). On the other hand,
\[
2^{(2r-1)s+1}
=2^{(2r-1)(s-1)+2r}
>3^{(2r-1)^2}2^{2r}
\ge3^{2r+1}2^{2r}
>2\cdot3^{2r}+5.
\]
Here \((2r-1)^2\ge2r+1\) for \(r\ge2\). Thus (6) holds, and
\[
\frac zM<
(2u-3)2^{-2rs}
<2^{1-s}
=\frac1{2^{s-1}}.
\]
Combining this with (5) gives \((z+R)/M<1\).

### Case 2: \((2r-1)s\ge a\)

Here \(M=2^{a+s}\). The upper-band hypothesis implies \(s\le a\), so (3) applies. Using \(D>M\) and \(S<2^{(2r-1)s+1}\),
\[
\begin{aligned}
\frac{z+R}{M}
&<\frac{Q}{M^2}+\frac RM\\
&<(2u-3)2^{(2r-2)s-2a}
  +3^{2r-1}2^{(2r-2)s+1-a}\\
&=2^{(2r-2)s-a}
  \left((2u-3)2^{-a}+2\cdot3^{2r-1}\right).
\end{aligned}
\]
By (3) and \(a\ge4r+3\), \((2u-3)2^{-a}<1\). By (4), the bracket is strictly less than \(2^{c_r}\). Finally,
\[
(2r-2)s\le a-c_r
\]
makes the leading factor at most \(2^{-c_r}\). Thus again \((z+R)/M<1\).

Both cases contradict (2). Therefore \(D\nmid N\), proving the theorem.

## Concrete intervals

| \(r\) | \(a_r\) | \(c_r\) | Excluded \(s\) | Excluded parent valuations \(u=v_r+s\) | Count |
|---:|---:|---:|---:|---:|---:|
| 2 | 43 | 6 | 6–18 | 48–60 | 13 |
| 3 | 367 | 9 | 9–89 | 375–455 | 81 |
| 4 | 3,283 | 13 | 13–545 | 3,295–3,827 | 533 |
| 5 | 29,527 | 16 | 16–3,688 | 29,542–33,214 | 3,673 |
| 6 | 265,723 | 19 | 19–26,570 | 265,741–292,292 | 26,552 |

The endpoints and counts follow directly from the theorem.

## Research significance and limits

This is an all-\(r\) arithmetic exclusion for a contiguous band of inverse valuations. It is distinct from the existing all-\(r\) high-valuation strip in im-results/agent20-needle-coprime/CancellationTopStrip.lean and the mod-20 exclusion in im-results/agent20-needle-coprime/CancellationMod5.lean. It can be combined with those results and with finite prime-witness sieves to reduce cancellation-feeder parent searches.

It does **not** exclude the remaining valuations, prove that any cancellation feeder is unreachable from the true blank start, prove Space Needle nonhalting, or determine BB(6). The result belongs in im-results/, not results/.

## Formalization target

A Lean formalization can reuse:

- CancellationNat.P and CancellationNat.exact from CancellationTopStrip.lean;
- CancellationConstructive.feederQ and feederQ_spec from CancellationTopConstructive.lean;
- CancellationTerminalConstructive.feederV, feederK, and exact_terminal_feeder;
- NeedleGeneralInverse.parent_successor_iff and the original-source inverse theorem in NeedleGeneralInverseSource.lean.

The key reusable lemma is the exact congruence
\[
2^{2rs}AP_r(A)\equiv3^{2r}\sum_{j<2r}2^{js}
\pmod{A2^s+3},
\]
followed by the two-modulus quotient bound above. No numerical parent enumeration is needed for this infinite-family theorem.
