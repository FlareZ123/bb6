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
d_r:=1+\left\lfloor\log_2(3^{2r-1})\right\rfloor.
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
\boxed{\quad d_r\le s,\qquad (2r-2)s\le a_r-d_r.\quad}
\]
Equivalently, the entire integer interval
\[
v_r+d_r\ \le u\le\
v_r+\left\lfloor\frac{a_r-d_r}{2r-2}\right\rfloor
\]
is excluded from the inverse-parent valuation set.

The interval is nonempty for every \(r\ge2\). First, \(3^{2r-1}<2^{4r-3}\), by induction from \(27<32\), so \(d_r\le4r-3\). Second, \(9^r\ge16r^2\) for \(r\ge2\), by induction from \(81\ge64\), so \(a_r\ge8r^2+5/2\). Hence
\[
a_r\ge(2r-1)(4r-3)\ge(2r-1)d_r.
\]

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

We need two elementary bounds. For \(r\ge2\),
\[
16^r>2\cdot9^r+5.
\tag{3}
\]
The base case is \(256>167\); the induction step multiplies the left side by \(16\) and the leading term on the right by \(9\). Also \(9^r\ge8r+1\), so \(a\ge4r+3\). In particular, whenever \(s\le a\),
\[
2u-3=3^{2r}+2s\le3^{2r}+2a=2\cdot9^r+5<2^{4r}<2^a.
\tag{4}
\]

Write \(n=3^{2r-1}\). By definition, \(2^{d_r}>n\). In fact,
\[
2^{d_r}\ge n+5.
\tag{5}
\]
The difference \(2^{d_r}-n\) is a positive odd integer. If it were \(1\), then \(n+1=2^{d_r}\). But for the odd exponent \(m=2r-1\ge3\),
\[
3^m+1=(3+1)(3^{m-1}-3^{m-2}+\cdots-3+1),
\]
where the second factor is odd and greater than \(1\), so \(3^m+1\) is not a power of two. If the difference were \(3\), then \(2^{d_r}=3^m+3\) would be divisible by three, also impossible. Since the gap is positive odd and cannot be 1 or 3, it is at least 5, proving (5).

For a Lean-friendly version of this factorization, define \(H_0=1\) and
\[
H_{t+1}=H_t+2\cdot3^{2t+1}.
\]
Induction gives \(3^{2t+1}+1=4H_t\); each increment is even, so \(H_t\) is odd, and \(H_t>1\) for \(t\ge1\). This proves the required non-power-of-two claim without alternating-sum subtraction.

For any \(s\ge d_r\), put
\[
T_s:=\frac{S}{2^{(2r-1)s}}
=\sum_{j=0}^{2r-1}2^{-js}.
\]
The finite geometric sum satisfies
\[
T_s<1+\frac1{2^s-1}.
\]
By (5), \(2^s\ge n+5\), so \(n/(2^s-1)<1\). Therefore
\[
nT_s<n+1\le2^s-4.
\tag{6}
\]
The same bound applies with any exponent \(m\ge d_r\) in place of \(s\):
\[
nT_s<n+1\le2^m-4.
\tag{7}
\]

We split according to which exponent defines \(M\).

### Case 1: \((2r-1)s\le a\)

Here \(M=2^{2rs}\), and \(s\le a\). Since \(D>M\),
\[
\frac zM=\frac{Q}{DM}<\frac{Q}{M^2}
<\frac{2u-3}{2^{2rs}}.
\]
By (4), this is less than \(2^{4r-2rs}\). More importantly, using \(2^s>n\),
\[
2^{(2r-1)s+1}
=2(2^s)^{2r-1}
>2n^{2r-1}
=2\cdot3^{(2r-1)^2}
>2\cdot3^{2r}+5
\ge2u-3.
\]
Here \((2r-1)^2\ge2r+1\) for \(r\ge2\). Hence
\[
\frac zM<(2u-3)2^{-2rs}<2^{1-s}=\frac2{2^s}.
\]
On the other hand, (6) and \(n+1\le2^s-4\) give
\[
\frac RM=\frac{nT_s}{2^s}<1-\frac4{2^s}.
\]
Thus \((z+R)/M<1\).

### Case 2: \((2r-1)s\ge a\)

Here \(M=2^{a+s}\). Put \(m=a-(2r-2)s\). The upper-band hypothesis says \(m\ge d_r\), and \(s\le a\). Since \(D>M\),
\[
\frac zM=\frac{Q}{DM}<\frac{Q}{M^2}
<(2u-3)2^{-a-m}.
\]
By (4), this is less than \(2^{-m}\), and hence less than \(2/2^m\). Meanwhile,
\[
\frac RM=\frac{nT_s}{2^m}<1-\frac4{2^m}
\]
by (7) and \(n+1\le2^m-4\). Thus again \((z+R)/M<1\).

Both cases contradict (2). Therefore \(D\nmid N\), proving the theorem.

## Concrete intervals

| \(r\) | \(a_r\) | \(d_r\) | Excluded \(s\) | Excluded parent valuations \(u=v_r+s\) | Count |
|---:|---:|---:|---:|---:|---:|
| 2 | 43 | 5 | 5–19 | 47–61 | 15 |
| 3 | 367 | 8 | 8–89 | 374–455 | 82 |
| 4 | 3,283 | 12 | 12–545 | 3,294–3,827 | 534 |
| 5 | 29,527 | 15 | 15–3,689 | 29,541–33,215 | 3,675 |
| 6 | 265,723 | 18 | 18–26,570 | 265,740–292,292 | 26,553 |

The endpoints and counts follow directly from the theorem.

## Research significance and limits

This is an all-\(r\) arithmetic exclusion for a contiguous band of inverse valuations. It is distinct from the existing all-\(r\) high-valuation strip in im-results/agent20-needle-coprime/CancellationTopStrip.lean and the mod-20 exclusion in im-results/agent20-needle-coprime/CancellationMod5.lean. It can be combined with those results and with finite prime-witness sieves to reduce cancellation-feeder parent searches.

The threshold is sharp for this particular quotient-size argument: if \(s<d_r\), then \(2^s\le n\) and the low-case term \(R/M=nT_s/2^s\) is already greater than one; similarly, if the complementary exponent \(m=a_r-(2r-2)s<d_r\), then \(2^m\le n\) and \(R/M=nT_s/2^m>1\). Improving either endpoint requires a different cancellation argument, not merely a sharper estimate of the same geometric sum.

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

For a Lean implementation that avoids modular-inverse APIs entirely, there is an explicit natural-number quotient certificate. Put \(t=2^s\), \(B=At\), and
\[
S_0=0,\qquad S_{r+1}=S_r+t^{2r}+t^{2r+1},
\]
\[
C_0=0,\qquad
C_{r+1}=B^2C_r+3^{2r}(B-3)S_r
       +9^rt^{2r}\bigl(t(A-3)-3\bigr).
\]
Then induction using \(P_{r+1}=A^2P_r+9^r(A-3)\) gives the exact identity
\[
t^{2r}AP_r(A)=3^{2r}S_r+(B+3)C_r.
\]
The two algebraic factorizations driving the induction are
\[
B^2-9=(B+3)(B-3),\qquad
t^2A(A-3)-9(1+t)=(B+3)(t(A-3)-3).
\]
For the present parameters \(A=2^{a_r}\ge8\) and \(t=2^s\ge2\), so all displayed natural subtractions are nonnegative. This certificate directly supplies the divisibility step in (1) and is a good starting point for a kernel-checked formalization.

The only small generic divisibility helper needed after (1) is
\[
2^m\mid 3x\quad\Longrightarrow\quad2^m\mid x.
\]
It can be proved in core Lean by induction on \(m\): the successor case first obtains \(2\mid3x\), uses \(\omega\) to deduce \(2\mid x\), writes \(x=2y\), cancels the leading factor two, and applies the induction hypothesis to \(3y\). The final contradiction can reuse CancellationTopStrip's \(Nat.not_dvd_of_pos_of_lt\) pattern.
