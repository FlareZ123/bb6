# Three M32-certified inverse-parent progressions for the Machine C thin gateway

**Status:** exact arithmetic reduction over the existing M32 quotient; the proposed combined Lean wrapper is not yet compiled. This is intermediate work, not a Machine C nonhalting proof and not a BB(6) result.

Let
\[
T_j=(0,2j,4j+10),\qquad q(x)=
\begin{cases}
x,&x<8,\\
8+(x-8)\bmod 32,&x\ge8.
\end{cases}
\]
The existing source bridge transports original BB6CLine.Reach into the kernel-checked B8/M32 closure. For a c=0 parent \((a,k,0)\), if \((q(a),q(k),0)\) is absent from that closure, the parent is unreachable.

The existing inverse-parent lemma draft zeroA_reach_parent in ThinGatewayM32.lean states that, for even \(K\ge8\), \(C\ge4\), and \(\operatorname{Reach}(0,K,C)\), one must have either
\[
C\equiv0\pmod2,\quad
\operatorname{Reach}\left(K+1,\frac{C+K-2}{2},0\right),
\]
or
\[
K\equiv0\pmod4,\quad
\operatorname{Reach}\left(0,\frac{K-4}{2},C+K+1\right).
\]
This is obtained by enumerating all predecessors of the finite descending high-counter chain. Its current proof has known Lean tactic/normalization errors documented in the 17 November CI log; the mathematical statement is not yet certified.

## Three infinite progressions

The M32 BFS has 31,570 reached abstract states and 189,834 representative edges, matching the already kernel-checked certificate. The following quotient cells are absent in that closure:
\[
(15,25,0),\ (33,20,0),\ (13,38,0),\
(25,13,0),\ (9,37,0),\ (25,29,0),\ (9,21,0).
\]
The first, third, and (9,37,0) are already used by the existing two-class wrapper; the other cells are directly checkable by the same finite certificate.

### 1. \(j=7+32n\)

Set \(K=2j=14+64n\), \(C=4j+10=38+128n\). The inverse-parent lemma gives either:

- the c=0 parent \((15+64n,25+96n,0)\), whose quotient is always \((15,25,0)\), absent; or
- the alternate branch, which would require \(K\equiv0\pmod4\), contradicting \(K\equiv2\pmod4\).

Thus this progression is excluded if the inverse-parent lemma and the M32 source bridge compile.

### 2. \(j=16+32n\)

Set \(K=32+64n\), \(C=74+128n\). The first c=0 parent is
\[
(33+64n,52+96n,0),
\]
whose quotient is \((33,20,0)\), absent.

The alternate branch is \((0,14+32n,107+192n)\). Its third coordinate is odd and its middle coordinate is \(2\pmod4\). Applying the inverse-parent lemma again makes both possible parents impossible. Hence this progression is excluded.

### 3. \(j=54+32n\)

Set \(K_0=108+64n\), \(C_0=226+128n\). The first c=0 parent
\[
(109+64n,166+96n,0)
\]
projects to absent cell \((13,38,0)\).

The alternate parent is
\[
U_0=(0,52+32n,335+192n).
\]
Its third coordinate is odd, while its middle coordinate is divisible by four, so the only viable inverse branch is
\[
U_1=(0,24+16n,388+224n).
\]
At \(U_1\), the c=0 parent is
\[
Q_1=(25+16n,205+120n,0).
\]
According to \(n\bmod4\), its quotient cycles through
\[
(25,13,0),\ (9,37,0),\ (25,29,0),\ (9,21,0),
\]
all absent. The remaining inverse branch is
\[
U_2=(0,10+8n,413+240n).
\]
Here the third coordinate is odd and the middle coordinate is \(2\pmod4\); since \(10+8n\ge10\), the inverse-parent lemma makes both possible parents impossible.

Thus all three progressions are candidates for an original-source nonreachability theorem. The small representative \(j=22\) is not included in the third progression; it is already excluded by the M512 computational sieve.

## Relation to the M512 gateway sieve

Modulo 256, these three progressions cover the classes:

- \(j\equiv7\pmod{32}\): 7, 39, 71, 103, 135, 167, 199, 231;
- \(j\equiv16\pmod{32}\): 16, 48, 80, 112, 144, 176, 208, 240;
- \(j\equiv22\pmod{32}\): 22, 54, 86, 118, 150, 182, 214, 246.

Comparing with the 116 M512-admitted residues in ThinGatewayM512.md, these progressions cover 20 of the 28 M512-only excluded residues and four M512-admitted residues (86, 103, 214, 231). Those four admitted residues are already covered by the existing \(j=86+128n\) and \(j=103+128n\) theorems. The value of the broader classes is therefore source-certifying most of the M512-only exclusions, not adding a new admitted gateway index.

## Lean acceptance boundary

A compact source wrapper can use one generic helper: if \(a,k\ge8\), their residues modulo 32 match an absent M32 cell \((u,v,0)\), then \(\operatorname{Reach}(a,k,0)\) is impossible. Prove the quotient equalities with CCert.q_congr_big, keep CCert.q opaque when rewriting reachable_seen, and use by decide for the seven absent cells.

The previous run 44132508910 successfully checked all eight M32 closure shards but failed in the downstream wrapper. It is not an acceptance run for these three progressions. The exact compiler diagnostics and suggested repairs are in the Agent 43 handoff at communications/agent43/20261117T191223Z_agent47-thin-gateway-ci-diagnosis.md. No new CI run should be dispatched until local Lean preflight is available.
