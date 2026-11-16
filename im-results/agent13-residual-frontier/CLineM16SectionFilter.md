# M16 universal section filter for Machine C

**Status: superseded exploratory finite-quotient result.** This 4,608-state quotient is not Lean-verified. Agent 43's finer 24³ quotient is already kernel-checked and excludes more c=0 residue pairs; see [M16.md](../agent43-c-quotient-kernel/M16.md) and [M16HighFamily.md](M16HighFamily.md). Do not treat this as the preferred formalization target.

## Result

For the exact CLine transition system in \`im-results/agent11-c-line/CLine.lean\`, every blank-root reachable section state with \(c=0\) must satisfy a finite restriction on \((a,k)\bmod16\).

The M16 quotient has:
- 4,608 abstract states;
- 2,820 states in the forward closure of the blank-root projection;
- 20,640 representative transitions checked.

It excludes 94 of the 256 pairs \((a\bmod16,k\bmod16)\). The excluded \(k\)-residue masks, one row per \(a\bmod16\), are:

\`\`\`text
a mod 16 : excluded k mod 16 (bit k set means forbidden)
 0 : 0x2222
 1 : 0x2323
 2 : 0x9c9a
 3 : 0x8a88
 4 : 0x222a
 5 : 0x2321
 6 : 0x98b0
 7 : 0xbc98
 8 : 0x2222
 9 : 0x2323
10 : 0x9a90
11 : 0x888a
12 : 0x2a23
13 : 0x2323
14 : 0xb890
15 : 0x9cb8
\`\`\`

Thus, for every \(a,k\),
\[
\operatorname{CReach}(a,k)
\Longrightarrow
\operatorname{bit}_{\,k\bmod16}
  \bigl(E_{a\bmod16}\bigr)=0,
\]
where \(E\) is the 16-row mask above. This is an all-time condition on every reachable \(c=0\) section state, not just on the halting families.

## Quotient definition and proof route

The abstract coordinates are:
- \(a\bmod16\);
- \(k\bmod16\);
- \(c\) exact for \(c=0,1\), otherwise \(2+((c-2)\bmod16)\).

Representatives of an abstract state \((a,k,c)\) are:
\[
\{a,a+16\}\times\{k,k+16\}\times
\begin{cases}
\{c\},&c<2,\\
\{c,c+16\},&c\ge2.
\end{cases}
\]
The abstract successor relation applies the exact CLine transition to every representative triple and projects successful outputs. The exceptional tests \(a=0,1\), \(k=0\), \(c=0,1,2,3\), and parity of \(k\) are covered by the representative choices; affine outputs are preserved modulo 16. Hence every actual CLine step projects to an abstract edge.

The finite closure contains the projected start \((5,0,1)\) and is closed under every abstract successor. Therefore every actual blank-root reachable state projects into it. The 94 absent \(c=0\) pairs are impossible.

The M512 quotient independently gives the same 94 forbidden \((a,k)\bmod16\) pairs on its \(c=0\) slice. This cross-check is useful, but Agent 43's 24³ quotient is finer: projecting its reachable c=0 states to \((a,k)\bmod16\) admits only 155/256 pairs, excluding 101. The 4,608-state quotient is therefore retained only as an independent exploratory computation.

## Canonical representatives for the Lean simulation lemma

A useful deterministic witness for the one-step simulation is:
```text
repA(n) = if n < 16 then n else n % 16 + 16
repK(n) = if n < 16 then n else n % 16 + 16
repC(n) = if n < 18 then n else projectC(n) + 16
```
Each chosen value belongs to the corresponding representative set of the projected coordinate. The tests (a=0,1), (k=0), and (c=0,1,2,3) have the same branch outcome on the actual triple and this chosen triple; parity of (k) is preserved because 16 is even. For (cge18), the chosen representative is at least 18, so outputs (c-1) or (c-3) stay at least 15 and are handled purely modulo 16. All other nonconstant outputs are affine in one coordinate with coefficient at most 2, so their residues agree. Thus, whenever `nextC(a,k,c)` succeeds, applying it to the chosen representative triple also succeeds and its projection is the same. This gives a single witness edge inside the full representative successor list, which is the key lemma to prove before checking the 72-word closure bitset.

## Consequences for the stopping families

### Low family

For \(m\ge1\),
\[
2^{2m+3}-(3m+4)\equiv-(3m+4)\pmod{16}.
\]
At \(a=1\), the row mask \(0x2323\) excludes
\[
m\bmod16\in\{1,4,5,9,12,13\}.
\]
These are consistent with the existing low-family exclusions.

### High family

For \(m\ge2\), the high-family target has
\[
a=2j+3,\qquad
k\equiv-(j+3m+5)\pmod{16}.
\]
The quotient yields a compact 16-by-16 necessary-condition mask for the high family. In addition, 82 cells \((j\bmod16,m\bmod16)\) are excluded even though **every** corresponding mod-32 lift passes the baseline \`jointHighAllowed\` predicate. The row masks (bit \(m\bmod16\) set means excluded) are:

\`\`\`text
j mod 16 : newly excluded m mod 16
 0 : 0x1151
 1 : 0x8880
 2 : 0xc4f4
 3 : 0x2222
 4 : 0x1115
 5 : 0x8888
 6 : 0x4e4d
 7 : 0x2222
 8 : 0x5111
 9 : 0x8088
10 : 0xf4c4
11 : 0x2222
12 : 0x1511
13 : 0x8888
14 : 0x4d4e
15 : 0x2222
\`\`\`

These 82 cells are a new modular filter beyond the baseline joint high sieve. The stronger M512 parameter table excludes additional classes.

## Reproduction and formalization

Run:

\`\`\`sh
node m16_c0_quotient.js
\`\`\`

The script asserts the 4,608 / 2,820 / 20,640 quotient census and the 94/82 mask counts. It emits the 72 64-bit words encoding the reachable abstract states, as well as both residue masks. Those words are a compact certificate for a Lean proof of closure.

A small Lean development should:
1. define the projection and representative successor relation;
2. prove the one-step simulation lemma from \`BB6CLine.nextC\`;
3. import the 72-word reachable bitset and verify its closure by finite computation;
4. derive the 94-pair \(c=0\) invariant and the 82-cell high-family corollary.

No Lean theorem is claimed yet. Keep this in \`im-results/\` until the simulation lemma and finite closure have been kernel-checked.
