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
In particular \(I_0\equiv6\pmod7\). Also, \(8^s\mid I_0\) gives the stronger 2-adic congruence
\[
2^{3s-1}\mid 7(k-3c)-25,\qquad
k-3c\equiv25\cdot7^{-1}\pmod{2^{3s-1}}.
\]
For example, \(s\ge1\) forces \(k-3c\equiv3\pmod4\), and \(s\ge2\) forces \(k-3c\equiv31\pmod{32}\). This is a congruence on the inverse parameters \(k,c\), not on \(m_0+n\); it does not reinstate the withdrawn false claim \(2^{3s-1}\mid(3-7(m_0+n))\) from the earlier restart draft.

Assume the same candidate wall-reaching suffix hypotheses as Agent 43's HighDepthRestartPotential.md, including its established positive lower bound on \(I_0\) for a suffix with at most five shallow edges. Thus \(0<I_0<98P\). Suppose the suffix begins with \(s\) depth-two edges. Their energy recurrence gives \(8^s\mid I_0\). Write
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

For a first shallow edge of depth \(e\in\{0,1\}\), the exact source-profile equations are
\[
\begin{aligned}
e=0:\quad&2I_1=I_s-588P+84T_1-232,\\
e=1:\quad&4I_1=I_s-392P+56T_1-136.
\end{aligned}
\]
Thus depth \(0\) requires \(2\mid I_s\), while depth \(1\) requires \(4\mid I_s\). In particular, the odd candidates \(I_s\in\{13,27,41\}\) cannot begin a shallow transition at all.

For \(I_s=6\) or \(34\), only depth \(0\) is possible. Its output \(I_1\) is odd for every \(T_1\), since the numerator is \(2\bmod4\). Such a state cannot continue through depths \(0,1,2\), and it cannot itself be the wall because wall energy is divisible by \(16\). These two candidate values are therefore excluded from any wall-reaching low-depth suffix.

For \(I_s=20\), depth \(1\) gives odd \(I_1\). Depth \(0\) gives
\[
I_1=(-588P+84T_1-212)/2,
\]
so \(I_1\equiv2\pmod4\) when \(T_1\) is even and \(4\mid I_1\) when \(T_1\) is odd. The even-\(T_1\) branch is now excluded completely: after the first depth-zero edge, the only possible next low edge is another depth-zero edge, whose output is odd. No wall endpoint can occur at either stage. The odd-\(T_1\) branch remains open.

For \(I_s=48\), exactly one first shallow depth can have output divisible by \(4\): depth \(0\) when \(T_1\) is even, and depth \(1\) when \(T_1\) is odd. The other first depth produces energy \(2\bmod4\) and cannot lead to the wall. This leaves one potentially continuing first-profile branch for either parity.

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
This may settle the parity-sensitive \(I_s=20\) branch once the allowable high-depth \(t\) values are sharpened. Since \(n\) is even in the P1 setting, \(m_0+n\equiv t\pmod2\) is equivalent to the \(m_0\equiv t\pmod2\) restriction already recorded in SourceWallToCarryDP.md §7.

## Bounding the high-depth edge under both terminal costs

Put
\[
M=m_0+n,\qquad D=d_0-1=c+3,\qquad
X=2^tD=d_p+b_p/2+3,
\]
and write \(A=98-2^\delta I_s\), so \(D_0=AP\). With \(q=b_p/2\) and \(d=d_p\), the exact parent-coordinate identities are
\[
49D+14M=AP+6,\qquad
d+2q+2M+11=14P+2t,\qquad
X=d+q+3,\qquad M\ge t+1.
\]
The last inequality is \(m_p+n\ge0\), since \(M=m_p+n+t+1\).

For a **cost-one** terminal shallow edge, the source bound gives
\[
128(M+3)<93P.
\]
The parent identities then imply
\[
128X>803P+128(t+1),\quad X<14P,\quad
49D\le AP+6,\quad
3136D+651P>64AP+3072.
\]
For \(P\ge2^{83}\), these inequalities and \(X=2^tD\) give:
- \(A=18\), i.e. \((\delta,I_s)=(2,20)\): \(t=5\) or \(6\);
- \(A=2\), i.e. \((\delta,I_s)=(1,48)\): \(t\ge8\).

For a **cost-two** terminal shallow edge, the source bound instead gives
\[
256(M+3)<77P.
\]
The same parent identities imply
\[
256X>1715P+256(t+1),\quad X<14P,\quad
49D\le AP+6,\quad
6272D+539P>128AP+6144.
\]
Again for \(P\ge2^{83}\), the resulting power-of-two bounds give:
- \(A=18\): \(t=5\) exactly;
- \(A=2\): \(t\ge8\).

Both sets of inequalities and all four depth conclusions are checked in RestartDepthBounds.lean. The file uses only natural-number arithmetic and the exact displayed parent-coordinate equations; it does not import or replace the original source induction.

| Last shallow cost | \((\delta,I_s)=(2,20)\) | \((\delta,I_s)=(1,48)\) |
|---|---:|---:|
| \(1\) | \(t=5\) or \(6\) | \(t\ge8\) |
| \(2\) | \(t=5\) | \(t\ge8\) |

The parity argument below removes the cost-one \(t=6\) branch. Thus the two terminal-cost cases have the same final residual families.

## Low-suffix closure and remaining cases

At the exact shifted wall \(W=12P\), the affine energy is
\[
I_{\rm wall}=49W-588P-112B+384=-112B+384,
\]
which is always divisible by \(16\). After the last depth-\(\ge3\) edge, all remaining transitions have depths \(0,1,2\). Their exact scalar recurrences are
\[
\begin{array}{c|c|c}
e & B' & \text{energy equation}\\ \hline
0 & B+1 & 2I'=I-588P+84B-232\\
1 & B+2 & 4I'=I-392P+56B-136\\
2 & B+3 & 8I'=I.
\end{array}
\]
The Lean leaf Mod7SlackLeaf.lean packages arbitrary finite sequences of these transitions as LowTrace and proves:
- odd energy cannot take any low-depth step and cannot equal wall energy;
- energy \(2\bmod4\) can only take a depth-zero step, after which the energy is odd;
- from \(I_s=20\) with even \(T_1\), either first shallow depth produces an energy from which no low-depth suffix can reach the wall;
- across the full mod-\(7\) candidate list, a wall-reaching low suffix requires \(I_s=20\) with odd \(T_1\), or \(I_s=48\).

The leaf was compiled locally with Lean 4.36.0-rc2. Its public theorem axiom lists are [propext, Quot.sound]; there is no sorryAx. It imports only Lean's arithmetic tactic, so this is a formal scalar-recurrence result, not an original-source CountCone theorem. Its hypotheses are exactly the displayed first-shallow equations and the restriction to depths \(0,1,2\) after the selected last high-depth restart.

Combining \(T_1\equiv t+s\pmod2\) with the large-\(P\) intervals gives the following residual cases, for either terminal shallow cost:
- \((\delta,I_s,t)=(2,20,5)\). Here \(n\equiv1\pmod3\) and \(n\) is even, so \(s=(n+2)/3\) is even. Thus \(T_1\equiv t\pmod2\); \(t=6\) is excluded and \(t=5\) remains. Its first shallow edge must have depth \(0\).
- \((\delta,I_s)=(1,48)\) with \(t\ge8\). Here \(n\equiv2\pmod3\) and \(n\) is even, so \(s=(n+1)/3\) is odd. If \(t\) is odd then \(T_1\) is even and the potentially continuing first shallow edge has depth \(0\); if \(t\) is even then \(T_1\) is odd and it has depth \(1\).

In particular, the \((\delta,I_s)=(1,20)\) branch is eliminated: its interval gives \(t=3\), while \(s\) is odd, so \(T_1\) is even. The remaining \((2,20,5)\) and \((1,48,t\ge8)\) branches are the only cases left by this reduction, whether the terminal shallow edge has cost one or two.

