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

## Corrected source parity gate (supersedes the withdrawn link)

The earlier parity argument in this section is withdrawn. In particular, \(b_p\equiv0\pmod4\) only gives \(q=b_p/2\) even; together with the power equation it gives \(d_p+q\equiv1\pmod4\), not \(d_p\equiv1\pmod4\). The claimed implications \(c\equiv1\pmod4\) for odd \(t\), \(c\equiv3\pmod4\) for even \(t\), and \(M=m_0+n\equiv t\pmod2\) do not follow. Consequently, the earlier claim that parity removes the cost-one \(t=6\) case is not established and must not be used.

There is a different valid congruence. Put \(D=c+3=d_0-1\) and \(M=m_0+n\). The exact restart identities are
\[
I_0=14k-42c-50,\qquad
D_0:=98P-I_0=49D+14M-6.
\]
In every six-bit-slack case with \(s\ge1\), \(I_0=8^sI_s\), hence \(8\mid I_0\). Also \(P=2^n\) is divisible by \(4\). Since \(D_0=(98-2^\delta I_s)P\), reduction of the second identity modulo \(4\), using \(D=c+3\), gives
\[
c+2M\equiv3\pmod4.
\]
Reduction of the first identity modulo \(8\) gives
\[
3k-c-1\equiv0\pmod4,\qquad c\equiv-k-1\pmod4.
\]
Combining these yields the correct relation
\[
\boxed{k\equiv2M\pmod4.}
\]
Equivalently, \(M\equiv k/2\pmod2\). This is a relation between the high-depth inverse left parameter and the restart time; it does not identify the restart-time parity with \(t\).

This congruence does not directly determine the first-shallow parent counter: the \(s\) depth-two transitions between the restart child and the first shallow edge intervene. The useful first-shallow coordinates are instead obtained from the exact energy and mass equations. At the state immediately before the first shallow edge, write its counters as \(b_s,d_s\), and let \(T_1=M+6+3s\). Then
\[
\begin{array}{ll}
I_s=20: & b_s+18=6d_s,\quad 7d_s+2T_1=14P+17,\\
I_s=48: & b_s+14=6d_s,\quad 7d_s+2T_1=14P+13.
\end{array}
\]
Let \(q_s=b_s/2\). Since \(P\) is divisible by \(4\), these equations give the following exact mod-\(4\) source restrictions:

- \(I_s=20\), \(T_1\) odd: \(d_s\equiv1\pmod4\), \(q_s=3d_s-9\equiv2\pmod4\). The first shallow edge is depth \(0\). Its source inverse equations give \(c_1=d_s+q_s\) and \(2k_1+2=q_s\), hence \(k_1\) is even. This branch is not eliminated by the immediate child-mod-\(4\) test.
- \(I_s=48\), \(T_1\) even: \(d_s\equiv3\pmod4\), \(q_s=3d_s-7\equiv2\pmod4\). The first shallow edge is depth \(0\). Again \(2k_1+2=q_s\), so \(k_1\) is even. This branch also survives the immediate child-mod-\(4\) test.
- \(I_s=48\), \(T_1\) odd: \(d_s\equiv1\pmod4\), \(q_s=3d_s-7\equiv0\pmod4\). The first shallow edge is depth \(1\). Its source equations give \(c_1=2d_s-5\). Crucially, the inverse-mass equation is \(2k_1+c_1+4=b_s+d_s\), not the depth-zero equation with constant \(+2\). It follows that \(2k_1=5d_s-13\), hence \(k_1\) is even and the child counter is divisible by \(4\). This branch therefore survives the immediate child-mod-four test.

**Formalization status:** RestartPath now retains the exact OddCone suffix, its inverse-depth/cost-list bridge, the absolute mass at the suffix root, and the equality between the RestartWalk origin and the suffix-root right counter. RestartWallLowTrace.lean now contains:
- oddCone_mass_from_start and oddCone_to_restartWalk, which propagate the absolute mass and reconstruct the scalar walk from the source suffix;
- oddCone_first_shallow_split and restartPath_first_shallow_source_split, which expose the actual first-shallow source parent, inverseAt guards, prefix-depth structure, and next-parent-or-wall child guard;
- restartPath_first_shallow_state, which identifies the first-shallow source right counter with the endpoint of the corresponding scalar RestartWalk prefix.

These new Lean interfaces have not yet been compiled in this invocation; local execution tools failed at the tool boundary, and CI dispatch is frozen pending local preflight. The first-shallow parity arithmetic above does not eliminate any candidate.

The remaining scalar candidates are all three first-shallow branches: \(I_s=20\) with odd \(T_1\) (first shallow depth \(0\), with \(\delta=1\) or \(2\); respectively \(n\equiv2\) or \(1\pmod3\), and odd or even \(s\)); and \(I_s=48\) with either parity of \(T_1\) (first shallow depth \(0\) when even, depth \(1\) when odd, \(\delta=1\), odd \(s\)). The specialized depth bounds below cover only \((\delta,I_s)=(2,20)\) and \((1,48)\); they do not cover \((1,20)\). The valid congruence \(k\equiv2M\pmod4\) remains useful, but does not yet distinguish these cases.

The two delta-one Is=20 terminal lemmas in [FirstShallowDeltaOneCostGate.lean](./FirstShallowDeltaOneCostGate.lean) are conditional on the extra hypothesis \\(M+3\\le P\\), where \\(M=m_0+n\\). The current `RestartPath` structure has no such field, and the checked source construction `restart_path_after_deep` does not derive it from its root-prefix argument. Thus these arithmetic lemmas do not presently exclude either terminal position. The earlier claim that \\(M+3\\le P\\) is an unconditional RestartPath bound is withdrawn. If an independent root-prefix theorem establishes it, the conditional consequences remain valid:
- Immediate first-shallow wall: \(M+n+2=14u\) and \(22u+4=3P\) imply \(11M+11n+50=21P\). Together with \(M+3\le P\), this gives \(10P\le11n+17\), contradicting \(P\ge2n\) and \(n\ge83\).
- Third-position A(0,0) wall: \(M+n+2=14u\) and \(21P=106u+32\) imply \(53M+53n+330=147P\). Together with \(M+3\le P\), this gives \(94P\le53n+171\), again contradicting \(P\ge2n\) and \(n\ge83\).
These arguments close only the stated terminal positions; arbitrary longer delta-one Is=20 LowTrace tails remain open.

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

For a **cost-one** terminal shallow edge, under the additional hypotheses \(K\le5\) and \(r\ge1\) (where \(r\) counts depth-two edges after the last shallow edge), the source bound gives
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

The previous parity argument removing the cost-one \(t=6\) branch is withdrawn; see the corrected source parity gate above. The terminal-cost bounds still give the displayed depth intervals, but the scalar and parent-coordinate files do not independently eliminate either value.

### First-shallow offset congruences

At the state after the \(s\) depth-two edges, let its counters be \(b_s,d_s\), and put \(T_1=M+6+3s\). The exact affine energy and mass identities give
\[
I_s=7(b_s-6d_s)+146,\qquad
b_s+d_s+2(M+3s)+13=14P.
\]
Thus \(I_s=20\) gives \(b_s+18=6d_s\), while \(I_s=48\) gives \(b_s+14=6d_s\). Eliminating \(b_s,d_s,M,s\) yields
\[
\begin{array}{ll}
I_s=20: & 7d_s+2T_1=14P+17,\quad T_1\equiv5\pmod7,\\
I_s=48: & 7d_s+2T_1=14P+13,\quad T_1\equiv3\pmod7.
\end{array}
\]
Combining with the already established parity of \(T_1\) sharpens this to \(T_1\equiv5\pmod{14}\) for \(I_s=20\); for \(I_s=48\), \(T_1\equiv10\pmod{14}\) when even and \(T_1\equiv3\pmod{14}\) when odd. These coordinate congruences are formalized in the Offset namespace of RestartDepthBounds.lean.



## Low-suffix closure and remaining cases

At the exact shifted wall \(W=12P\), the affine energy is
\[
I_{\rm wall}=49W-588P-112B+384=-112B+384,
\]
which is always divisible by \(16\). After the last depth-\(\ge3\) edge, all remaining transitions have depths \(0,1,2\). The sign-dynamics lemma also forces at least one later shallow edge before the wall, because a depth-two-only suffix preserves positive defect. Thus the first-shallow profile is non-vacuous. Their exact scalar recurrences are
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

The source first-shallow split has **three** residual branches, not two:
- \((\delta,I_s)=(2,20)\), odd \(T_1\), first shallow depth zero;
- \((\delta,I_s)=(1,48)\), even \(T_1\), first shallow depth zero;
- \((\delta,I_s)=(1,48)\), odd \(T_1\), first shallow depth one.

The odd-\(T_1\) \(I_s=48\) branch is **not** eliminated by the first-child mod-four guard: `is48_odd_first_shallow_even_child` proves that its child parameter is even, so the child satisfies the required mod-four condition. Keep it as a separate residual branch. The new second-shallow gate below refines all three branches. The terminal-cost bounds give \(t=5\) or \(6\) for the \((2,20)\) family and \(t\ge8\) for the \((1,48)\) family, subject to their stated cap hypotheses.

## Second-shallow source gate (new arithmetic reduction)

Let \(P=2^n\). In the three first-shallow branches write the first-shallow parent offset as \(T\), and set \(T=14u+5\), \(14u+10\), or \(14u+3\), respectively. Solving the source-wall mass equation together with the mod-seven source-coordinate relation gives the following first-shallow parent and child coordinates:

| Branch | Parent \((b,d)\) | First-shallow child \((b_1,d_1)\) | \(X_1=d_1+b_1/2+3\) |
|---|---|---|---|
| \(I_s=20,\ T=14u+5\) | \((12P-24u-12,\ 2P-4u+1)\) | \((6P-12u-12,\ 8P-16u-1)\) | \(11P-22u-4\) |
| \(I_s=48,\ T=14u+10\) | \((12P-24u-20,\ 2P-4u-1)\) | \((6P-12u-16,\ 8P-16u-7)\) | \(11P-22u-12\) |
| \(I_s=48,\ T=14u+3\) | \((12P-24u-8,\ 2P-4u+1)\) | \((10P-20u-12,\ 4P-8u+1)\) | \(9P-18u-2\) |

Here \(X_1\) is the source coordinate for the next inverse edge. The child source coordinate identity is \(X_1=c+k+5\), where the first-shallow inverse parameters are \(k,c\). The child parameter \(k\) is even in all three branches.

### The first-shallow child cannot itself be the wall

Write \(M\) for the restart offset before the depth-two prefix and \(D\) for the even restart defect parameter. The restart defect equations are
\[
49D+14M=18P+6\quad(I_s=20),\qquad
49D+14M=2P+6\quad(I_s=48),
\]
with \(D\ge4\). The prefix length gives
\[
M+n+3=14u\quad(I_s=20),
\]
\[
M+n=14u+3\quad(I_s=48,\ T\text{ even}),
\qquad
M+n+4=14u\quad(I_s=48,\ T\text{ odd}).
\]
If the first-shallow child were already the wall, its wall equation \(b_1+4B_1=12P+4\), with \(B_1=T+1\) or \(T+2\), would give respectively
\[
22u+4=3P,\qquad 22u+12=3P,\qquad 18u+2=P.
\]
Each terminal equation contradicts the corresponding restart defect equation and \(D\ge4\), provided \(2n\le P\). The Lean lemma `target_power_bound` proves this in the target range \(P=2^n,\ n\ge83\). Thus the first-shallow child is not the wall: a further source edge must follow.

### Exact next-edge residue gate

For that next edge, let its depth be \(t\in\{0,1,2\}\), with inverse parameters \(k,c\). The source equations and child guards are
\[
2^t(c+3)=X_1,\qquad c\equiv1\pmod2,\qquad
2k+c+2t+2=b_1+d_1,\qquad k\equiv0\pmod2.
\]
The last condition is exactly the next child's required \(b\equiv0\pmod4\). Lean proves the following necessary residue conditions:

| First-shallow branch | Next depth \(t=0\) | Next depth \(t=1\) | Next depth \(t=2\) |
|---|---|---|---|
| \(I_s=20,\ T=14u+5\) | \(u\equiv0\pmod2\) | \(u\equiv0\pmod4\) | \(u\equiv2\pmod8\) |
| \(I_s=48,\ T=14u+10\) | \(u\equiv1\pmod2\) | \(u\equiv2\pmod4\) | \(u\equiv2\pmod8\) |
| \(I_s=48,\ T=14u+3\) | \(u\equiv0\pmod2\) | \(u\equiv3\pmod4\) | \(u\equiv3\pmod8\) |

These are necessary conditions, not sufficient existence criteria: the remaining inverseAt lower bounds and source-history conditions still apply. The arithmetic is formalized in [FirstShallowCoordinateGate.lean](./FirstShallowCoordinateGate.lean), compiled locally with Lean 4.36.0-rc2 using only the Lean core. It is not yet composed into a single theorem over the original RestartPath witness.

## Boundary

The mod-\(7\) classification and low-suffix closure remain conditional on the high-depth restart equations, the positive restart-energy bound \(0<I_0<98P\), and the existence of a wall-reaching suffix with at most five shallow edges. The depth intervals and three first-shallow branches use the appropriate cost-one or cost-two terminal bound and \(P\ge2^{83}\). The scalar recurrence and arithmetic leaves formalize necessary conditions, but the source restart wrapper is not yet compiled and no residual branch has been excluded. This is not a BB(6) result.

The remaining mathematical task is to compose the second-edge residue gate with the authentic RestartPath witness and propagate it through the next low-depth transitions, or to prove a stronger source-prefix cost bound. Do not repeat the mod-\(7\) enumeration or terminal-cost arithmetic.
