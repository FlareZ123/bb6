# Two-parameter inverse-kernel sieve for last-reset branches 1–7

**Status: intermediate computational research, not a formal result.** This dossier records a reproducible reduction of the seven constant-seed last-reset cases. The source-level last-reset characterization is formalized elsewhere; the two-parameter affine certificate used here is currently a JavaScript generalization of the one-parameter Lean kernel and still needs a Lean soundness proof.

## Basis

- Exact source-level last-reset characterization: \`im-results/agent32-429-turnaround-gap/BB429LastResetEquation.lean\`
- Existing one-parameter inverse kernel and terminal root predicates: \`im-results/agent1-429-root-rows/BB429InverseKernelExtended.lean\`

The prototype lifts
\[
(u,w)=(Aq+a,\;Bq+b)
\]
to
\[
(u,w)=(A_1q_1+A_2q_2+a,\;B_1q_1+B_2q_2+b),
\qquad q_1,q_2\in\mathbb N.
\]
The inverse transformations F/S/E are applied coefficientwise. A family is marked *excluded* only when every inverse path reaches one of the existing terminal root obstructions within the specified depth. A family not excluded by this bounded procedure is **unresolved**, not reachable.

The terminal predicates mirror the current \`BB429InverseKernelExtended.lean\` implementation: the mod-8 reachable-pair table, positive-even mod-8 restriction, and established mod-16/mod-32 low-row obstructions. No unverified root lemmas are added.

## Exact last-reset branch equations

Write the last-reset prestate as \((x,y)\), with burst length \(n\ge18\). The seven cases are:

| Branch | Prestate shape | \(n\bmod4\) | Exact equation |
|---:|---|---:|---|
| 1 | \(y=2x+2\) | 3 | \(4x=3\cdot2^{n+2}-3n-31\) |
| 2 | \(y=2x+1\) | 1 | \(4x=14\cdot2^{n+2}-3n-37\) |
| 3 | \(y=2x\) | 1 | \(4x=3\cdot2^{n+2}-3n-25\) |
| 4 | \(y=2x-2\) | 1 | \(4x=3\cdot2^{n+2}-3n-21\) |
| 5 | \(y=2(x-d),\ d=2e,\ e\ge1\) | 1 | \(4x=14\cdot2^{n+2}+4e-3n-33\) |
| 6 | \(y=2(x-d),\ d=2e+1,\ e\ge1\) | 1 | \(4x=3\cdot2^{n+2}+4e-3n-21\) |
| 7 | \(y=2x-3\) | 3 | \(4x=3\cdot2^{n+2}-3n-15\) |

## Affine family coverage

### Branches 1–4 and 7: burst quotient plus residue split

Put \(n=4t+3\) for branches 1 and 7, and \(n=4t+1\) for branches 2–4. The lower bounds are respectively \(t\ge4\) and \(t\ge5\).

For split width \(k\), write
\[
t=t_0+r+2^k s,\qquad 0\le r<2^k,\quad s\ge0,
\]
where \(t_0=4\) or \(5\). Set
\[
Q=256^{\,2^k s}-s-1\ge0.
\]
Then every prestate in the branch belongs to the two-parameter affine family
\[
x=CQ+(C-3\cdot2^k)s+a,\qquad y=2x+c,
\]
where
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

Thus
\[
(A_1,A_2,a)=(C,\ C-3\cdot2^k,\ a),\qquad
(B_1,B_2,b)=(2C,\ 2(C-3\cdot2^k),\ 2a+c).
\]
This is an over-approximation because \(Q\) and \(s\) are treated as independent nonnegative parameters. Every actual \(n\) in the branch is covered.

### Branches 5 and 6: split the half-gap and burst residue

Write \(n=4t+1\), \(t\ge5\), and let \(d=2e\) in branch 5 or \(d=2e+1\) in branch 6, with \(e\ge1\). Put \(r=y/2\). Then \(x=r+2e\) in branch 5 and \(x=r+2e+1\) in branch 6.

For split width \(k\), write
\[
t=t_0+2^k s,\quad t_0=5+r_t,\qquad
e=e_0+2^k p,\quad 1\le e_0\le2^k.
\]
Let \(r_0\) be the least residue modulo \(2^k\) of
\[
28\cdot256^{t_0}-3t_0-9-e_0
\]
in branch 5, or
\[
6\cdot256^{t_0}-3t_0-7-e_0
\]
in branch 6. Since \(r\ge0\), write \(r=r_0+2^kq\), \(q\ge0\). The resulting affine families are
\[
x=2^kq+2^{k+1}p+r_0+2e_0+\delta,\qquad
y=2^{k+1}q+2r_0,
\]
where \(\delta=0\) in branch 5 and \(\delta=1\) in branch 6. This covers every admissible \(t,e\), while allowing the quotient parameters \(q,p\) to vary independently.

## Current bounded-sieve output

### Branches 1–4 and 7

These use a staged refinement:
1. Split \(t\) modulo \(2^{14}\) and run depth 14.
2. For each unresolved first-stage residue, split its four lifts modulo \(2^{16}\) and run depth 16.

| Branch | Stage-1 families | Stage-1 excluded | Stage-1 unresolved | Stage-2 child families | Stage-2 excluded | Stage-2 unresolved |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 16,384 | 16,278 | 106 | 424 | 424 | 0 |
| 2 | 16,384 | 16,298 | 86 | 344 | 344 | 0 |
| 3 | 16,384 | 16,270 | 114 | 456 | 456 | 0 |
| 4 | 16,384 | 16,276 | 108 | 432 | 432 | 0 |
| 7 | 16,384 | 16,296 | 88 | 352 | 352 | 0 |

Thus the JS prototype discharges all five of these branches at the staged bounded depth. This remains conditional on formalizing the two-parameter kernel.

The long-burst implementation uses 96-bit residues. Each inverse step loses at most two precision bits; after 16 steps at least 64 bits remain, while every terminal predicate inspects at most 32 bits. The \`large\` flag is also justified throughout: the smallest initial affine constant is branch 1 at \(t=4\), \(24\cdot256^4-22>2^{36}\). Along F, the first coordinate changes to \((a-3)/2\); along S/E it changes to \(a+b/4-O(1)\), with \(b\ge0\). Even 16 consecutive F steps leave it above \(2^{20}\), so all depth-16 uses of \(a\ge13\) and \(a>0\) are valid.

For \(t\ge12\), each coefficient \(K\cdot256^t\) is divisible by \(2^{96}\), so replacing it by zero in the 96-bit residue representation is exact. For \(t<12\), the script computes the exact residue.

### Branches 5 and 6

These use exact BigInt arithmetic, split \(t,e\) modulo \(2^9\), and inverse depth 14.

| Branch | Affine families | Excluded by prototype | Unresolved |
|---:|---:|---:|---:|
| 5 | 262,144 | 247,936 | 14,208 |
| 6 | 262,144 | 249,685 | 12,459 |

The branch-5/6 grid has two residue parameters, so its family counts are not directly comparable to the one-residue grids above.

## Reproduction

Run with Node.js:

\`\`\`sh
node im-results/agent32-429-last-reset-affine2/affine2_sieve.mjs > affine2-sieve-output.json
\`\`\`

Environment variables:
- \`LONG_BITS\` (default 14; first-stage split for branches 1–4 and 7)
- \`LONG_DEPTH\` (default 14)
- \`LONG_CHILD_BITS\` (default 16)
- \`LONG_CHILD_DEPTH\` (default 16)
- \`GAP_BITS\` (default 9; branches 5 and 6)
- \`GAP_DEPTH\` (default 14)

The output includes all unresolved first-stage offsets, child offsets, and branch-5/6 parameter pairs.

## What is and is not established

1. The seven algebraic branch equations are transcribed from the formal last-reset characterization.
2. The affine parametrizations above cover the corresponding branch families exactly; the inverse sieve then deliberately over-approximates by freeing quotient parameters.
3. The staged exclusion counts are reproducible computational evidence from the JavaScript prototype.
4. **No new Lean theorem is claimed here.** In particular, the two-parameter analogue of \`cert_sound\` has not yet been proved. Until that generalization is formalized and compiled, the five-branch discharge and the branch-5/6 exclusion counts are not proven non-reachability results.
5. The unresolved branch-5/6 families are not asserted reachable. They are simply not discharged by this bounded certificate.

## Highest-value next step

Generalize the existing \`Affine\`/\`cert_sound\` development in \`BB429InverseKernelExtended.lean\` to a finite coefficient vector (or at least \`Affine2\`), prove the coefficientwise F/S/E equations and the corresponding soundness theorem, then replay the exact family tables in Lean. Once the five-branch discharge is formal, spend inverse depth and stronger root obstructions only on branches 5 and 6 and their emitted unresolved pairs.
