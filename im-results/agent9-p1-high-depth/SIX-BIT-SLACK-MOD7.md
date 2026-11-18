# Mod-7 reduction of the high-depth restart six-bit slack

**Status: conditional arithmetic reduction, not a completed high-depth exclusion.** This note uses the restart variables and energy identity from Agent 43's HighDepthRestartPotential.md. It does not prove the source restart wrapper or settle the remaining one-bit-slack branch.

## Exact restart energy in parent inverse coordinates

Let a depth-\(t\ge3\) inverse edge have parent \((b_p,d_p,m_p)\), inverse parameters \((k,c)\), and restart child
\[
(b_0,d_0,m_0)=(2k-4,c+4,m_p+t+1).
\]
Use the source equations
\[
b_p+d_p+2m_p+2n+13=14P,\qquad
2k+c+2t+2=b_p+d_p,
\]
and restart energy
\[
I_0=98P-49d_0-14(m_0+n)+55.
\]
Substitution gives the exact identity
\[
\boxed{I_0=14k-42c-50=2\bigl(7(k-3c)-25\bigr).}
\]
In particular \(I_0\equiv6\pmod7\).

Suppose the suffix begins with \(s\) depth-two edges. Their energy recurrence gives \(8^s\mid I_0\). Write
\[
\delta=3s-n,\qquad I_s=I_0/8^s\in\mathbb N.
\]
The high-depth restart bound \(I_0<98P\) gives \(3s\le n+6\), so \(\delta\le6\). In the six-bit-slack cases \(\delta>0\), we have
\[
I_0=2^{n+\delta}I_s,\qquad
D_0:=98P-I_0=(98-2^\delta I_s)P>0.
\]
Since \(8^s\equiv1\pmod7\), the exact energy identity gives
\[
I_s\equiv6\pmod7.
\]
Positivity of \(D_0\) gives \(0<I_s<98/2^\delta\). Since \(\delta\equiv-n\pmod3\), the complete list of six-bit-slack cases is therefore:

| \(n\bmod3\) | possible \(\delta=3s-n\) | possible \(I_s\) |
|---:|---:|---:|
| 0 | 3 | 6 |
| 0 | 6 | none |
| 1 | 2 | 6, 13, 20 |
| 1 | 5 | none |
| 2 | 1 | 6, 13, 20, 27, 34, 41, 48 |
| 2 | 4 | 6 |

Thus the nominal six-bit slack reduces to \(\delta\le4\), with only the displayed small post-prefix energies. The corresponding \(D_0/P=98-2^\delta I_s\) values are also finite:
- \(n\equiv0,\delta=3\): \(D_0/P=50\).
- \(n\equiv1,\delta=2\): \(D_0/P\in\{74,46,18\}\).
- \(n\equiv2,\delta=1\): \(D_0/P\in\{86,72,58,44,30,16,2\}\).
- \(n\equiv2,\delta=4\): \(D_0/P=2\).

## First-shallow profile filter

For a first shallow edge of depth \(e\in\{0,1\}\), use the source profile equations
\[
\begin{aligned}
e=0:\quad&2I_1=I_s-588P+84T_1-232,\\
e=1:\quad&4I_1=I_s-392P+56T_1-136.
\end{aligned}
\]
For \(n\ge3\), \(P=2^n\) is divisible by 8, and the non-\(I_s\) terms in both numerators are divisible by 4. Consequently:
- depth \(e=0\) requires \(I_s\) even;
- depth \(e=1\) requires \(4\mid I_s\).

This immediately eliminates \(I_s=13\). If \(I_s=6\), only \(e=0\) is possible, and
\[
I_1=(-588P+84T_1-226)/2
\]
is odd for either parity of \(T_1\): modulo 8 its numerator is \(6+4T_1\), so \(I_1\equiv1\) or \(3\pmod4\). Hence no following depth-two run (which requires \(8\mid I_1\)) and no second shallow edge (which requires \(2\mid I_1\) for depth 0 or \(4\mid I_1\) for depth 1) can follow this branch.

If \(I_s=20\), depth 1 gives an odd \(I_1\), since its numerator is \(20\pmod8\). Depth 0 gives
\[
I_1=(-588P+84T_1-212)/2,
\]
whose residue modulo 4 is \(2\) when \(T_1\) is even and \(0\) when \(T_1\) is odd. Thus the only potentially continuing branch in the \(\delta=2\) case is \(I_s=20\), first shallow depth 0, with odd \(T_1\). This is not excluded here.

For the \(\delta=1\), \(n\equiv2\pmod3\) case, the seven possible values \(I_s\) remain to be analyzed beyond this first-profile filter. This is the main residual branch after the mod-7 reduction.

## A useful parity link for the restart time

In the same source setup, \(b_p\equiv0\pmod4\), \(k\) is even, \(c\) is odd, and
\[
2^t(c+3)=d_p+b_p/2+3.
\]
For \(t\ge2\), this gives \(d_p\equiv1\pmod4\). The inverse cost equation then gives
\[
c\equiv1\pmod4\quad(t\text{ odd}),\qquad
c\equiv3\pmod4\quad(t\text{ even}).
\]
In a slack case, \(D_0=(98-2^\delta I_s)P\) is divisible by 4. Since
\[
D_0=49d_0+14(m_0+n)-55,\qquad d_0=c+4,
\]
reduction modulo 4 shows
\[
m_0+n\equiv t\pmod2.
\]
If the restart-shifted first profile time is \(T_1=m_0+n+6+3s\), this yields
\[
T_1\equiv t+s\pmod2.
\]
This may settle the parity-sensitive \(I_s=20\) branch once the allowable high-depth \(t\) values are sharpened.

## Boundary

This note only narrows the six-bit slack and filters the first shallow profile. It does not exclude the remaining \(\delta=1\) cases, the potentially continuing \(I_s=20\) branch, or all wall-reaching suffixes. It is not a source-certified theorem or a BB(6) result. The next useful check is whether the exact restart model can exploit the finite \(I_s\) list and the \(T_1\equiv t+s\pmod2\) relation without reintroducing the full six-bit model.
