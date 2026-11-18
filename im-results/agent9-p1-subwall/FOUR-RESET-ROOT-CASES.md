# Conditional arithmetic closure of the four-reset offset-wall root cases

**Status: paper-only arithmetic lemma, 2026-11-18.** This note closes the remaining root-power subcases listed in Agent 50's [four-reset-offset-exploration.md](../agent50-p1-subwall/four-reset-offset-exploration.md). It assumes that the preceding source peeling has already established the displayed root equations and cost bounds. It does **not** prove the preceding peeling, a CountCone source wrapper, a six-reset floor, P1 nonhalting, or a BB(6) bound. Keep it in im-results.

Let \(P=2^n\), \(n\ge14\), \(2\le m_1\le3n+4\), and \(r\le m_1\). Let \(B,D\in\mathbb N\) satisfy
\[
B+D+2r+2n+13=14P,\qquad
2^r(B+12)+2n+4=14P,\qquad
4\mid B.
\]
Set
\[
L=D+B/2+3.
\]
The first inverse power equation in the four-reset peel requires
\[
L=2^u C_1,\qquad u\ge1.
\]

There are two formulas for \(C_1\), according to the upper-tail case:
- \(s_1=0\): \(C_1=2P+1170m_1+1170n+13542\).
- \(s_1=1\): \(C_1=-5P+1170m_1+1171n+13546\).

The following proves that neither case is possible under the displayed assumptions.

## Case \(s_1=0\)

Here \(C_1=2P+1170m_1+1170n+13542\).

The root equations give \(L<14P\), while \(C_1\ge2P\). Hence \(2^u=L/C_1<7\), and \(u\in\{1,2\}\).

### \(r=0\)

The root equations give
\[
B=14P-2n-16,\quad D=3,\quad L=7P-n-2.
\]
The choice \(u=2\) would give \(L=4C_1\ge8P\), contradicting \(L<7P\). Thus \(u=1\), and \(L=2C_1\) is equivalent to
\[
3P=2340m_1+2341n+27086. \tag{1}
\]
This is impossible in all ranges:
- \(n=14\): the right side is at least \(2340\cdot2+2341\cdot14+27086=64540\), whereas \(3P=49152\).
- \(n=15\): equation (1) forces \(2340m_1=36103\), but \(36103=2340\cdot15+1003\).
- \(n\ge16\): since \(m_1\le3n+4\), the right side of (1) is at most \(9361n+36446\). The inequality
  \[
  3\cdot2^n>9361n+36446
  \]
  holds at \(n=16\) and then by induction for all \(n\ge16\), contradicting (1).

### \(r=1\)

The root equations give
\[
L=(21P-3n-10)/2.
\]
Again \(u\in\{1,2\}\).

If \(u=1\), then
\[
13P=4680m_1+4683n+54178. \tag{2}
\]
Reducing (2) modulo 8 gives \(n\equiv2\pmod8\). Reducing modulo 13 gives \(n\equiv2\pmod{13}\). Hence \(n\equiv2\pmod{104}\), and \(n\ge106\). But the right side of (2) is at most \(18723n+72898\), while
\[
13\cdot2^n>18723n+72898
\]
already at \(n=106\) and by induction thereafter. Contradiction.

If \(u=2\), then
\[
5P=9360m_1+9363n+108346. \tag{3}
\]
Modulo 8, equation (3) gives \(n\equiv2\pmod8\), so \(n\) is even. Modulo 3, it gives \(2(-1)^n\equiv1\pmod3\), so \(n\) is odd. Contradiction.

### \(r\ge2\), \(n\ge18\)

The second root equation and \(4\mid B\) imply
\[
2^{r+2}\mid 14P-2n-4.
\]
For \(n\ge14\), since \(0<n+2<2^n\),
\[
v_2(14P-2n-4)=1+v_2(n+2).
\]
This valuation will handle the small indices below.

For \(n\ge18\), the root equations also give
\[
8L+16r+14n+28\ge98P.
\]
Using \(r\le m_1\le3n+4\),
\[
L\ge(98P-62n-92)/8.
\]
On the other hand,
\[
4C_1\le8P+18720n+72888.
\]
The inequality
\[
34\cdot2^n>149822n+583196 \tag{4}
\]
holds at \(n=18\) and by induction for every \(n\ge18\). Comparing the preceding two bounds with (4) gives \(4C_1<L\). Also \(L<14P<16P\le8C_1\). Thus
\[
4C_1<L<8C_1,
\]
which is incompatible with \(L=2^uC_1\).

### \(r\ge2\), \(14\le n\le17\)

The divisibility \(2^{r+2}\mid14P-2n-4\) and the valuation formula give
\[
r\le v_2(n+2)-1.
\]
For \(n=15,16,17\), this upper bound is respectively \(-1,0,-1\), so no \(r\ge2\) is possible.

For \(n=14\), it gives \(r\le3\), leaving \(r=2,3\). Here \(P=16384\), and direct substitution in the root equations gives:
\[
(r,B,L)=(2,57324,200672),\qquad
(r,B,L)=(3,28656,215004).
\]
Also
\[
C_1=62690+1170m_1,\qquad 65030\le C_1\le116510.
\]
In both cases \(L<4C_1\), while \(u\ge1\); hence \(u=1\) and \(C_1=L/2\). But
\[
100336-62690\equiv206\pmod{1170},
\]
and
\[
107502-62690\equiv352\pmod{1170}.
\]
Neither remainder is zero, contradicting \(C_1=62690+1170m_1\).

This completes \(s_1=0\).

## Case \(s_1=1\)

Now
\[
C_1=-5P+1170m_1+1171n+13546.
\]
Using \(m_1\le3n+4\),
\[
C_1\le-5\cdot2^n+4681n+18226.
\]
The inequality \(5\cdot2^n>4681n+18226\) holds at \(n=15\) and by induction for all \(n\ge15\). Thus \(C_1<0\) for \(n\ge15\), impossible because \(C_1=c_1+3\ge6\).

At \(n=14\), \(P=16384\) and
\[
C_1=1170m_1-51980.
\]
Positivity together with \(m_1\le46\) forces \(m_1\in\{45,46\}\), giving \(C_1=670\) or \(1840\).

The root divisibility and \(4\mid B\) give \(2^{r+2}\mid229344\). Since \(v_2(229344)=5\), \(0\le r\le3\). The four exact root lengths are
\[
L\in\{114672,172006,200672,215004\}.
\]
If \(C_1=670\), the only power-of-two multiple \(2^uC_1\), \(u\ge1\), in this interval is \(2^8\cdot670=171520\), which is not one of the four lengths. If \(C_1=1840\), the only such multiple is \(2^6\cdot1840=117760\), also absent. Contradiction.

This completes \(s_1=1\).

## Consequence and boundary

Conditional on Agent 50's preceding four-reset peel establishing the displayed equations and bounds, the two final upper-tail root cases \(s_1=0,1\) are arithmetically impossible. The proof uses only exact integer inequalities, congruences and the explicitly listed small cases. It remains a paper derivation until integrated into the authentic CountCone source proof and checked in Lean. It should not be cited as a six-reset floor.
