# M512 all-time quotient sieve for Machine C source parameters

**Status: intermediate computational all-time exclusion; not Lean-formalized.** This is a source-connected finite-quotient result, not a decision of Machine C or BB(6). It belongs in \`im-results/\`.

## Exact source families being screened

The source-certified blank-root criterion in \`im-results/agent3-c-bounce-inverse/ValSixJointFull.lean\` reduces a physical Machine C halt to one of two CLine section targets:

- Low family:
  \[
  \operatorname{CReach}\bigl(1,\;2^{2m+3}-(3m+4)\bigr).
  \]
- High family:
  \[
  \operatorname{CReach}\bigl(2j+3,\;2^{2m+2}(j+3)-(j+3m+5)\bigr).
  \]

Separately, the authentic cylinder equivalence in Agent 4's source dossier reduces the physical halt to a thin gateway
\[
T_j=(0,2j,4j+10).
\]

All three targets are tested against the same M512 over-approximation of the exact CLine map, starting at \((5,0,1)\).

## Quotient and soundness boundary

The quotient uses:
- \(a\bmod512\);
- \(k\bmod512\);
- \(c\) exact for \(c=0,1\), otherwise \(2+((c-2)\bmod256)\).

The representative sets are \(\{a,a+512\}\), \(\{k,k+512\}\), and \(\{c\}\) for \(c<2\), otherwise \(\{c,c+256\}\). The quotient successor relation applies the exact CLine transition to every representative triple and projects each successful output.

The exceptional branch tests \(a=0,1\), \(k=0\), \(c=0,1,2,3\), and the parity of \(k\) are preserved by these representatives. Every affine output is respected modulo the corresponding modulus; when subtraction crosses the low boundary, the second representative captures the high lift. Consequently every genuine CLine transition projects to one of the quotient edges. The quotient is an over-approximation: absence of a projected target proves non-reachability, while presence proves nothing about genuine reachability.

The finite closure has 67,633,152 vertices, 27,858,704 reached vertices, and 221,572,376 representative edges. These counts match Agent 19's independently recorded M512 quotient census.

## All-time parameter exclusions

### Low family

For \(m\ge5\), \(2^{2m+3}\equiv0\pmod{512}\), so the projected target depends only on \(m\bmod512\). Scanning one complete period gives:

- 190 admitted residues;
- **322 excluded residues**.

Thus for every \(m\ge5\),
\[
\operatorname{CReach}(1,2^{2m+3}-(3m+4))
\Longrightarrow m\bmod512\in L,
\]
where \(L\) is the 190-element allowed list printed by the reproduction script.

The small cases \(m=0,1,2,3,4\) are checked using their exact target values. The quotient admits \(m=0,2\) and excludes \(m=1,3,4\).

### High family

For \(m\ge4\), \(2^{2m+2}\equiv0\pmod{512}\), hence the projected target depends only on \((j\bmod512,m\bmod512)\). The full 512-by-512 scan gives:

- 262,144 residue pairs;
- 107,446 quotient-admitted pairs;
- **154,698 excluded pairs** (about 59.0%).

Therefore every genuine high-family witness with \(m\ge4\) must lie in the 107,446 admitted cells of this residue table. The exact table is emitted as \`M512HighAdmittedMask.bin\` by the script; bit \((m\bmod512)\cdot512+(j\bmod512)\) is 1 precisely when the quotient admits the pair. The script also reports the SHA-256 digest and all 512 row counts, so the table can be reproduced and checked.

The four small high parameters \(m=0,1,2,3\) are scanned separately using their exact exponent. Their admitted/excluded counts are respectively \(198/314,\ 227/285,\ 195/317,\ 221/291\) across \(j\bmod512\).

### Thin gateway

The target \(T_j=(0,2j,4j+10)\) has period 256 in the quotient. Exactly 116 residue classes are admitted and **140 are excluded**. The complete allowed list is in \`ThinGatewayM512.md\`.

## Reproduction

Run from this directory:

\`\`\`sh
node m512_parameter_sieve.js
\`\`\`

The script asserts the quotient census and all three target-scan counts, emits the low/thin residue lists and high row counts, and writes the 32 KiB high-family admission bitmask. It uses the same representative transition relation as Agent 19's \`QuotientRectCensus.cpp\`.

## What this does and does not establish

This is an infinite congruence sieve, not a finite forward simulation: the periods above cover every lift of the relevant parameters. It narrows both unbounded stopping families and the thin gateway, and can be added as a necessary condition to the existing exact halting criterion.

It does **not** show that any admitted target is reachable, eliminate every low or high parameter, or prove Machine C nonhalting. The quotient closure and the source-to-quotient simulation are not yet Lean-formalized. Keep this as intermediate computational evidence until an independently checked proof or certificate is supplied.

