# M512 quotient sieve for the Machine C thin halting gateway

**Status: intermediate computational all-time exclusion; not Lean-formalized.** This belongs in \`im-results/\`, not \`results/\`. It does not decide Machine C or BB(6).

## Target and source connection

The authentic Machine C cylinder reduction in Agent 4's source dossier proves that a physical halt in the 25-completion root cylinder requires the original three-counter section to reach a thin gateway
\[
T_j=(0,2j,4j+10)
\]
for some \(j\ge0\). The section transition is the exact \`BB6CLine.nextC\` in \`im-results/agent11-c-line/CLine.lean\`, starting at \((5,0,1)\).

This note gives a new necessary congruence condition on that \(j\), using the already existing M512 quotient graph from \`im-results/agent19-c-odd-dyadic/QuotientRectCensus.cpp\`.

## Quotient

Use abstract coordinates
- \(a\bmod512\);
- \(k\bmod512\);
- \(c\) exact for \(c=0,1\), and otherwise represented by \(2+((c-2)\bmod256)\).

For an abstract state \((a,k,c)\), the representative sets are
\[
\{a,a+512\},\qquad \{k,k+512\},\qquad
\begin{cases}
\{c\},&c<2,\\
\{c,c+256\},&c\ge2.
\end{cases}
\]
Apply the exact \`nextC\` transition to every representative triple and project each successful output back into the quotient. This gives a finite nondeterministic over-approximation: every genuine transition from a state represented by a quotient vertex is represented by at least one quotient edge. The extra representatives preserve the exceptional tests \(a=0,1\), \(k=0\), \(c=0,1,2,3\), and the parity test on \(k\); the affine outputs are respected modulo the corresponding powers of two.

The quotient has exactly 67,633,152 vertices. Breadth-first closure from the projected blank-root state \((5,0,1)\) visits 27,858,704 vertices and checks 221,572,376 representative edges. These three counts independently match Agent 19's existing M512 census, providing a cross-check that the thin-target scan uses the same finite graph.

## Infinite residue exclusion

For every \(j\), the projected target \((0,2j,4j+10)\) depends only on \(j\bmod256\). Scanning one complete period gives 116 admitted residue classes and 140 excluded classes.

The **only** residues not excluded by this quotient are:
\[
\begin{aligned}
S=\{&
0,2,8,10,11,14,15,18,23,24,26,27,30,31,32,34,\\
&38,40,42,43,46,47,50,55,56,62,63,64,66,70,72,74,\\
&75,78,79,82,86,87,88,90,91,94,95,96,98,102,103,104,\\
&106,107,110,111,114,119,120,122,126,127,128,130,136,\\
&138,139,142,143,146,151,152,154,155,158,159,160,162,\\
&166,168,170,171,174,175,178,183,184,190,191,192,194,\\
&198,200,202,203,206,207,210,214,215,216,218,219,222,\\
&223,224,226,230,231,232,234,235,238,239,242,247,248,\\
&250,254,255\}.
\end{aligned}
\]

Therefore
\[
\operatorname{Reach}(0,2j,4j+10)
\quad\Longrightarrow\quad
j\bmod256\in S.
\]
Equivalently, all 140 residues in \(\{0,\ldots,255\}\setminus S\) are excluded for **every** lift \(j+256n\), not merely for a finite range of \(j\). This is an infinite congruence sieve for the authentic root trajectory, obtained from a finite over-approximation rather than a bounded forward simulation.

Combining this with the source-connected physical-cylinder equivalence, any physical halt in the authentic 25-completion Machine C cylinder must use a thin-gateway index \(j\) in \(S\).

## Reproduction and limitations

Run:

\`\`\`sh
node thin_gateway_m512.js
\`\`\`

The script asserts the three M512 census counts before reporting the 116/140 target split. It uses the same state encoding, representative sets, and transition cases as Agent 19's C++ quotient implementation.

This is a computational quotient result, not a Lean theorem. The soundness argument is the finite case analysis described above; an independent Lean formalization or proof-carrying closure certificate would strengthen it. An admitted residue means only that the quotient cannot exclude the target; it does **not** establish actual reachability.

The inverse-tree relation in \`ThinGatewayInverse.md\`,
\[
j+2=4^m(j'+3),
\]
also shows a limitation: for \(m\ge4\), every such deep inverse branch has \(j\equiv254\pmod{256}\), and \(254\in S\). Thus this M512 sieve does not close the deep second-family tail. It is a genuine reduction of the thin-gateway index space, not a complete Machine C decision.

