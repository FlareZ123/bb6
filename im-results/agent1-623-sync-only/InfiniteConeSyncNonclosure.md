# Infinite original-source cone-to-cone S-window synchronization failures (#623)

**Status:** a genuine unbounded mathematical counterfamily to a proposed *universal* invariant, derived from original-source LE high-level transitions and established signed-drain identities. The all-depth theorem is paper-proved here but not yet a single source-imported Lean theorem. Its states are **synthetic**, not claimed blank-root-reachable. No decision of #623 or BB(6).

## Exact statement

Put \(\tau(h)=(3^h-1)/2\). For a section state \(D(a,d)\), let \(S=a+d\), \(\ell_S=\min\{h:S+3\le\tau(h)\}\), \(B=34\ell_S+122\), \(k=\min\{h:3^h>B\}\), \(j=\min\{h:3^h>B^3\}\), \(s=k+2\), \(P=3^s\), \(n=j-k-4\), \(M=3^n\).

For \(p=|a-d|,\ q=\min(a,d)\), sector phase \(\gamma=(18,10,2,4)\) (LO/LE/RO/RE), write \(X=2(p-3q)-\gamma,\ Y=6q\). The **actual moving S-window word** is \((x,y)=([\lfloor X/P\rfloor]_M,[\lfloor Y/P\rfloor]_M)\). Both full carry rectangles synchronize precisely when the four inequalities of [ExactSynchronizationCriterion.md](ExactSynchronizationCriterion.md) hold.

**Theorem.** For **every** integer \(\ell\ge20\), there is an even \(q>0\) such that the **original** accelerated #623 rule executes a successful transition
\[
\boxed{D(4q+20\ell,q)\longrightarrow D(a',d')}
\]
with both source and target satisfying the source-certified **newAffineCone**, the source mass depth \(\ell_S=\ell\), and source word \((x,y)=(0,1)\), which synchronizes **both** full carry rectangles. Nevertheless the target word satisfies
\[
[x'+y']_{3^{n'-1}}\in\{0,-1\},
\]
so the target **right** full rectangle does **not** synchronize. The family is unbounded. Therefore the implication “source cone, target cone and source S-window synchronization imply target S-window synchronization” is **mathematically false**, even for source-faithful successful transitions.

## Constructing even q at every depth

Fix \(\ell\ge20\), \(c=20\ell\), \(B=34\ell+122\), and its \(k,j,P,M,n\) as above. Since \(B\ge802\), \(k\ge7\). Since \(j\ge3k-2\), \(n\ge2k-6\ge8\).

Because \(M=3^n\) is odd, pick \(t_0\in\{1,3\}\) with \(1+Mt_0\equiv0\pmod4\). For \(r\ge0\), let
\[
t=t_0+4r,\qquad q_r=\frac{3^{k+1}(1+Mt)}2.
\]
Each \(q_r\) is a positive **even** integer and \(6q_r=P(1+Mt)\). Consecutive q values have gap \(G=2\cdot3^{j-3}\). The exact depth condition \(\ell_S=\ell\), since \(S=5q+c\), is
\[
\frac{\tau(\ell-1)-c-3}{5}<q\le
\frac{\tau(\ell)-c-3}{5}.
\tag{1}
\]
This interval has length \(3^{\ell-1}/5\). By minimality of \(j\),
\[
G=\tfrac29 3^{j-1}\le\tfrac29 B^3<3^{\ell-1}/5.
\]
The final inequality holds at \(\ell=20\) (RHS \(232452293.4\), LHS bound \(114633246.22\ldots\)) and persists by induction: \(3^{\ell-1}\) triples, but \(B_{\ell+1}^3/B_\ell^3\le(4/3)^3<3\). The interval (1) starts positive, has length \(>G\), and its right endpoint exceeds the first progression term \(0<q_0<G\). It therefore contains one of the even \(q_r\).

For this q the source state is far-left even with \(p=3q+c\); hence \(X=2c-10=40\ell-10\in[0,P)\) because \(P=9\cdot3^k>9B\). Also \(Y=P(1+Mt)\). The source S-window is exactly \((x,y)=(0,1)\pmod M\), regardless of the size of q. Its four synchronization residues are \(M-3,3,1,1\), all allowed for \(n\ge8\). The source is in newAffineCone: \(d=q\) is even, \(a-d=3q+c\ge3\), and \(q+2\le\tau(a-d-2)=\tau(3q+c-2)\).

## Actual source drain and target non-synchronization

The **original** highLevelNext LE rule is
\[
\mathrm{highLevelNext}(D(4q+c,q))
=\mathrm{drainB}(3q+c-2,\ q+2,\ 2).
\tag{2}
\]
The source-certified drain digit normal form for this successful drain has length \(L\), number \(n_1,n_2\) of output digits 1 and 2, signed first-counter drop \(D=L-2n_2\), and evaluator count \(R=n_1+n_2\). Its exact output is
\[
(a',d')=(3q+c-2-D,\quad3q+8+2D+2R).
\tag{3}
\]
Since \(2(q+2)-1=2q+3<3^\ell\), the valuation length lemma \(3^{L-1}\le2(q+2)-1\) gives \(L\le\ell\), so \(|D|\le\ell\), \(0\le R\le\ell\), and \(D+2R=L+2n_1\ge0\).

Set \(T=3D+2R+10\); then \(|T|\le5\ell+10\) and
\[
p'=a'-d'=c-T\in[15\ell-10,25\ell+10]\subset(0,\infty).
\tag{4}
\]
The target is LE since \(d'=3q+8+2D+2R\) is even. With \(q'=d'\), we have \(0<q'\le3q+4\ell+8\), whence \(q'+2\le\tau(\ell+2)\) for \(\ell\ge20\) (use \(q\le\tau(\ell)/5\)), and \(p'-2\ge15\ell-12\ge\ell+2\). Thus \(q'+2\le\tau(p'-2)\), proving the **target itself is in the original LE cone**, not merely a numerically valid output.

The exact mass increase is
\[
S'-S=q+D+2R+6>0.
\]
Therefore \(\ell'_S\ge\ell\) and its target window scale \(P'=3^{k'+2}\ge P>9B\). The global signed sum coordinate is
\[
V'=X'+Y'=2p'-10\in[30\ell-30,50\ell+10]\subset(0,P').
\tag{5}
\]
For *any* signed integers \(X',Y'\), the exact floor-carry relation is
\[
\lfloor X'/P'\rfloor+\lfloor Y'/P'\rfloor
=\lfloor (X'+Y')/P'\rfloor-c'_V,\qquad c'_V\in\{0,1\},
\]
where \(c'_V=\mathbf1_{((X'+Y')\bmod P')<(Y'\bmod P')}\). Equation (5) makes the right-hand side \(0\) or \(-1\). Thus the target digit-word form \([x'+y']_{3^{n'-1}}\) is a **forbidden right-scale residue**. This proves the all-\(\ell\) theorem without any carry-transducer simulation, and shows exactly where a root-specific invariant is indispensable.

## Two-call concrete original-source certificate

A smaller source-authentic counterexample is
\[
\boxed{\mathrm{highLevelNext}(D(4388,1094))=D(3284,3310).}
\]
Its original LE dispatch is \(\mathrm{drainB}(3292,1096,2)\) and uses **only two** evaluator calls:

| Drain input \((a,b,d)\) | Original evalA output |
| --- | --- |
| \((3292,1096,2)\) | \(\mathrm{evalA}(3292,1095,2197)=(3291,365,2199)\) |
| \((3291,365,2199)\) | \(\mathrm{evalA}(3291,364,2932)=(3284,0,3310)\) |

Both endpoints are in newAffineCone (input LE, output RE). Their actual mass windows have \((\ell,k,j,n,P,M)=(9,6,17,7,6561,2187)\). Source digit word \((0,1)\) synchronizes; target \((2184,3)\) fails because \((2184+3)\bmod729=0\).

The first \(\ell=20\) family member has \(q=150666804,c=400\) and
\[
D(602667616,150666804)\to D(452000798,452000456).
\]
Both are LE cone states; its input word is (0,1), its target word is (6558,3), with sum zero modulo 2187.

## Reproducibility, limits and research implication

[verify_cone_sync_failure_family.js](verify_cone_sync_failure_family.js) is a BigInt arithmetic implementation of the **original** evalA/drainB/highLevelNext recursion, independent of the canonical p,q cocycle. It checks the small witness and the family at every \(\ell=20,\ldots,50\), including both cone budgets, exact source-defined moving windows, and the four synchronization residues. Those finite checks corroborate the analytic proof; they do not establish its universal quantifier.

This source-connected result **refutes universal cone-level synchronization preservation** and redirects attempted #623 invariants toward real blank-root history/reachability. It does not refute the root-only synchronization conjecture: none of these synthetic states is claimed to occur on that orbit. The tiny equality above is a suitable narrow future source-imported Lean certificate; the combined all-depth theorem is **not** claimed source-compiled.
