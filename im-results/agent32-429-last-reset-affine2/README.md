# Two-parameter inverse-kernel sieve for last-reset branches 1–7

**Status: intermediate computational research, not a formal result.** This directory records a reproducible reduction of the seven constant-seed last-reset cases. The source-level last-reset characterization is formalized elsewhere; the two-parameter affine certificate used here is currently a JavaScript/BigInt generalization of the one-parameter Lean kernel and still needs a Lean proof.

## What this computes

The input is the exact last-reset equation and branch split in:

- \`im-results/agent32-429-turnaround-gap/BB429LastResetEquation.lean\`
- the one-parameter inverse kernel and its terminal root predicates in \`im-results/agent1-429-root-rows/BB429InverseKernelExtended.lean\`

The prototype lifts the latter kernel from
\[
(u,w)=(Aq+a,\;Bq+b)
\]
to two independent nonnegative parameters:
\[
(u,w)=(A_1q_1+A_2q_2+a,\;B_1q_1+B_2q_2+b).
\]
The inverse transformations are applied coefficientwise. A family is marked *excluded* only when every inverse path reaches one of the same terminal root obstructions used by the existing kernel within depth 14. A family not excluded by this bounded procedure is **unresolved**, not reachable.

The terminal predicates mirror the current \`BB429InverseKernelExtended.lean\` implementation: the mod-8 reachable-pair table, positive-even mod-8 restriction, and the established mod-16/mod-32 low-row obstructions. The script deliberately does not add unverified root lemmas.

## Exact family parametrizations

Write the last-reset prestate as \((x,y)\), and let \(n\ge18\) be the reset burst length. The seven cases are:

| Branch | Prestate shape | \(n\bmod4\) | Exact equation |
|---:|---|---:|---|
| 1 | \(y=2x+2\) | 3 | \(4x=3\cdot2^{n+2}-3n-31\) |
| 2 | \(y=2x+1\) | 1 | \(4x=14\cdot2^{n+2}-3n-37\) |
| 3 | \(y=2x\) | 1 | \(4x=3\cdot2^{n+2}-3n-25\) |
| 4 | \(y=2x-2\) | 1 | \(4x=3\cdot2^{n+2}-3n-21\) |
| 5 | \(y=2(x-d),\ d=2e,\ e\ge1\) | 1 | \(4x=14\cdot2^{n+2}+4e-3n-33\) |
| 6 | \(y=2(x-d),\ d=2e+1,\ e\ge1\) | 1 | \(4x=3\cdot2^{n+2}+4e-3n-21\) |
| 7 | \(y=2x-3\) | 3 | \(4x=3\cdot2^{n+2}-3n-15\) |

### Branches 1–4 and 7: burst quotient plus residue split

Put \(n=4t+3\) for branches 1 and 7, and \(n=4t+1\) for branches 2–4. The lower bounds are respectively \(t\ge4\) and \(t\ge5\).

For a split width \(k\), write
\[
t=t_0+r+2^k s,\qquad 0\le r<2^k,\quad s\ge0,
\]
where \(t_0=4\) or \(5\). Set
\[
Q=256^{\,2^k s}-s-1\ge0.
\]
For the relevant branch constants \(K\) and \(c\), each prestate is in the two-parameter affine family
\[
x=CQ+(C-3\cdot2^k)s+a,\qquad y=2x+c,
\]
with
\[
C=K\,256^{t_0+r},\qquad a=C-3(t_0+r)-h.
\]

| Branch | \(K\) | \(h\) | \(c\) |
|---:|---:|---:|---:|
| 1 | 24 | 10 | 2 |
| 2 | 28 | 10 | 1 |
| 3 | 6 | 7 | 0 |
| 4 | 6 | 6 | -2 |
| 7 | 24 | 6 | -3 |

The family coefficients are therefore
\[
(A_1,A_2,a)=(C,\ C-3\cdot2^k,\ a),\qquad
(B_1,B_2,b)=(2C,\ 2(C-3\cdot2^k),\ 2a+c).
\]
This is an over-approximation because \(Q\) and \(s\) are treated as independent nonnegative parameters. Every actual \(n\) in the branch is nevertheless covered.

### Branches 5 and 6: split the half-gap and burst residue

Write \(n=4t+1\), \(t\ge5\), and let \(d=2e\) in branch 5 or \(d=2e+1\) in branch 6, with \(e\ge1\). Define
\[
r=\begin{cases}
x-d,&\text{branch 5},\\
x-d,&\text{branch 6}.
\end{cases}
\]
Then \(y=2r\), and \(x=r+2e\) in branch 5, \(x=r+2e+1\) in branch 6.

For split width \(k\), write
\[
t=t_0+2^k s,\quad t_0=5+r_t,\quad
e=e_0+2^k p,\quad 1\le e_0\le2^k.
\]
Since \(256^t\equiv0\pmod{2^k}\),
\[
r\equiv -3t_0-9-e_0\pmod{2^k}
\]
in branch 5, and
\[
r\equiv -3t_0-7-e_0\pmod{2^k}
\]
in branch 6. Let \(r_0\) be the least nonnegative residue and write \(r=r_0+2^kq\), \(q\ge0\). The resulting affine families are
\[
x=2^kq+2^{k+1}p+r_0+2e_0+\delta,\qquad
y=2^{k+1}q+2r_0,
\]
where \(\delta=0\) in branch 5 and \(\delta=1\) in branch 6. This covers every admissible \(t,e\), while again allowing the quotient parameters \(q,p\) to vary independently.

## Current bounded-sieve counts

The script uses inverse depth 14 and exact JavaScript \`BigInt\` arithmetic.

| Branch | Split width \(k\) | Affine families | Excluded by the prototype | Unresolved |
|---:|---:|---:|---:|---:|
| 1 | 12 | 4,096 | 4,034 | 62 |
| 2 | 12 | 4,096 | 4,046 | 50 |
| 3 | 12 | 4,096 | 4,038 | 58 |
| 4 | 12 | 4,096 | 4,042 | 54 |
| 5 | 9 | 262,144 | 247,936 | 14,208 |
| 6 | 9 | 262,144 | 249,685 | 12,459 |
| 7 | 12 | 4,096 | 4,044 | 52 |

These are counts of affine parameter families, not counts of machines or reachable states. In particular, the branch-5/6 parameter grid has two residue parameters, whereas the other five branches have one.

## Reproduction

Run with Node.js:

\`\`\`sh
node im-results/agent32-429-last-reset-affine2/affine2_sieve.mjs > affine2-sieve-output.json
\`\`\`

Environment variables can change the inverse depth and split widths:
- \`DEPTH\` (default 14)
- \`LONG_BITS\` (default 12; branches 1–4 and 7)
- \`GAP_BITS\` (default 9; branches 5 and 6)

The output includes every unresolved residue offset/pair, so later work can target only the remaining families.

## What is and is not established

1. The seven algebraic branch equations are transcribed from the formal last-reset characterization.
2. The affine parametrizations above cover the corresponding branch families exactly (the inverse sieve then deliberately over-approximates by freeing quotient parameters).
3. The numerical exclusion counts are reproducible computational evidence from this JavaScript port.
4. **No new Lean theorem is claimed here.** In particular, the two-parameter analogue of \`cert_sound\` has not yet been proved. Until that generalization is formalized and compiled, the table is a research sieve, not a proof that the excluded families are unreachable.
5. The unresolved families are not asserted to be reachable. They are simply not discharged by this depth-14 certificate.

## Highest-value next step

Generalize the existing \`Affine\`/ \`cert_sound\` development in \`BB429InverseKernelExtended.lean\` to a finite coefficient vector (or at least \`Affine2\`), prove the coefficientwise F/S/E equations and the corresponding soundness theorem, then replay the exact family tables in Lean. After that, spend inverse depth and stronger root obstructions only on the unresolved offsets/pairs emitted by this script. Branches 5 and 6 are the largest remaining workload.
