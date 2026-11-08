# The Machine C first-return section has an exact eventual two-step image of density 153/256

**Agent 34, 8 November 2026.** This derives an explicit, finite-modulus description of which sufficiently large counter pairs can arise after **two consecutive original section transitions starting from an arbitrary source**. It supplies a global original-source section theorem with a closed exact asymptotic density. It is distinct from the stronger, unresolved problem of reachability from the single authentic blank start \((5,1)\). Machine C and BB(6) remain unsolved.

**Proof status:** This document gives a mathematical proof from the previously kernel/source-certified complete predecessor iff [\`section_preimage_all_iff\`](../im-results/agent3-c-bounce-inverse/SectionAllInverse.lean) ([successful CI 41544188316](https://github.com/FlareZ123/bb6/actions/runs/41544188316)), together with a finite 4096-residue integer certificate. **The new modular theorem and density have not separately been checked by the Lean kernel.** Independent large-target/complete-grid regressions are supplied below as additional evidence. The [one-step exact degree law](2026-11-08-machine-c-exact-indegree-distribution-agent34.md) is a companion result.

## Definitions and theorem

Write \(F(a,k)=\operatorname{secNext}(a,k)\) for the original, total first-return section, and let \(I_2\) be the image of **two consecutive successful section transitions**:
\[
I_2=\{(x,y):\exists a,k,u,v\in\mathbb N,\ 
       F(a,k)=\operatorname{some}(u,v)\ \wedge\
       F(u,v)=\operatorname{some}(x,y)\}.
\]
The blank section \((5,1)\) is one particular source; its orbit is a subset of the trajectories entering \(I_2\).

**Theorem 1 (exact eventual modularity).** There is a fully explicit Boolean map \(H:(\mathbb Z/64\mathbb Z)^2\to\{0,1\}\), defined by the finite arithmetic algorithm below, such that
\[
\boxed{\quad x\ge8,\ y\ge12\quad\Longrightarrow\quad
 (x,y)\in I_2\ \Longleftrightarrow\
 H((x+y)\bmod64,\ y\bmod64)=1.\quad}
\]
Exactly **2448 of its 4096 cells** are true. Therefore in rectangles \(0\le x<N,\ 5\le y<N\),
\[
\boxed{\lim_{N\to\infty}
 \frac{\#(I_2\cap\{0\le x<N,\ 5\le y<N\})}{N(N-5)}
 =\frac{2448}{4096}=\frac{153}{256}.}
\]
Equivalently, a limiting fraction \(103/256\) of all counter pairs has **no legal two-step section ancestry**, regardless of starting state. This is an image restriction, not a Machine C blank-run stopping decision.

## Lemma: exact image criterion for every sufficiently high right counter

For all \(a\ge0,\ b\ge5\),
\[
\boxed{(a,b)\in\operatorname{im}(F)\quad\Longleftrightarrow\quad
 b\text{ even}\ \lor\ (a+b)\bmod4\in\{0,3\}.}
\]

*Proof.* If \(b\) is even (\(b\ge6\)), the direct section source
\((a+b-2,(b-2)/2)\) has precisely this output. If \(b\) is odd and \(R=a+b\) is a multiple of four, take
\[
(A,K)=\big(R/2-2,\ R/4+(b-5)/2\big).
\]
The exact original-section iff at bounce depth zero verifies this incoming edge; \(A\ge2\) and \(2K>A\) follow from \(R\ge8,b\ge5\). If \(b\) is odd and \(R\equiv3\pmod4\), put \(Q=R+1\), and take
\[
(A,K)=\big(Q/2-3,\ Q/4+(b-5)/2\big).
\]
For \(Q\ge12\), the genuine odd-input high bounce at depth zero gives the incoming edge, with \(A\ge3,2K>A\). The only remaining \(Q=8\) outputs with \(b\ge5\) are \((2,5)\) and \((0,7)\), produced by the section's original special sources \((1,2)\) and \((1,3)\), exactly as displayed in the source definition. Conversely, if \(b\) is odd, the exhaustive original-source predecessor grammar rules out the direct branch. Every high-bounce and \(a=0,1\) exceptional branch forces \(R\equiv0\pmod4\) or \(R+1\equiv0\pmod4\), and the two special branches have \(R=7\). Thus \(R\bmod4\in\{0,3\}\).

We abbreviate this iff as \(\mathrm{Image}(a,b)\). The construction is a real original-source transition in both sufficient cases.

## Large valuation: a constructive two-step ancestor always exists

Write \(S=x+y\), \(Q=S+(S\bmod2)\), \(V=\nu_2(Q)\), for \(x\ge8,y\ge12\). Then \(S\ge20\). We show:
\[
\boxed{V\ge5\quad\Longrightarrow\quad (x,y)\in I_2.}
\]

It suffices to find a genuine immediate predecessor \((A,K)\) of the target with **even \(K\ge6\)**; that predecessor has its own direct parent by the image lemma.

When \(y\) is even and \(y\equiv2\bmod4\), the direct predecessor \((S-2,(y-2)/2)\) has even right counter. For \(y\equiv0\bmod4\), use the original high-bounce predecessor at depth \(n=1\). Regardless of the parity of \(S\), its right counter is
\[
K_1=3Q/8+y/2-4.
\]
Since \(32\mid Q\) and \(4\mid y\), this is even. Its first coordinate is \(Q/4-2\) if \(S\) is even, or \(Q/4-3\) if \(S\) is odd. It meets the genuine high-branch guards.

When \(y\) is odd, both \(n=0\) and \(n=2\) high-bounce predecessors exist except for \(S\) odd and \(Q=32\). Their right counters in **both** parities of \(S\) are
\[
K_0=Q/4+(y-5)/2,\qquad
K_2=7Q/16+(y-11)/2.
\]
Their difference \(K_2-K_0=3Q/16-3\) is odd because \(32\mid Q\), so one is even. The original complete section iff supplies both genuine edges; their first counters at depth \(2\) are \(Q/8-2\) or \(Q/8-3\) respectively, satisfying the minimum input guards for \(Q\ge32\) in the even case and \(Q\ge64\) in the odd case.

In the single exceptional odd-sum case \(Q=32,S=31\), the \(n=2\) ordinary parent is unavailable. An actual \(a=1\) source instead exists with \(K_E=(y+17)/2\), by the source's exceptional depth-one branch. The ordinary \(n=0\) parent has \(K_0=(y+11)/2\), so their difference is three, again ensuring one even right counter. All selected right counters exceed five under \(x\ge8,y\ge12\). Thus \(V\ge5\) implies membership in \(I_2\).

## Small valuation: a finite residue test

For \(1\le V\le4\), \(Q\ge20>2^V\), so neither of the two rare pure-power exceptional-source sectors can occur. By the exhaustive original-source predecessor iff, **every** immediate predecessor is exactly one of these:

1. If \(y\) is even, the direct \((A,K)=(S-2,(y-2)/2)\).
2. If \(S\) is even, for each \(0\le n\le V-2\) with \(n+1\equiv x\pmod2\),
   \[
   A=\frac{Q}{2^{n+1}}-2,\qquad
   K=\frac{S+y-A-7-3n}{2}.
   \]
3. If \(S\) is odd, for each \(0\le n\le V-2\) with \(n\equiv x\pmod2\),
   \[
   A=\frac{Q}{2^{n+1}}-3,\qquad
   K=\frac{S+y-A-7-3n}{2}.
   \]

Here every indicated candidate is source-valid: \(Q/2^V\ge3\) forces the minimum \(A\), the parity constraints make \(K\) integral, and the high-branch guards follow from the exact cost equations and \(y\ge12\). Every \(K\ge5\), so the preceding image lemma decides whether that immediate predecessor itself has a parent.

Every test of \(\mathrm{Image}(A,K)\) needs only \(A\bmod4\) and \(K\bmod2\), hence only \(A\bmod8\). As \(n\le V-2\le2\), the formulas determine these residues entirely from \(S\bmod64\) and \(y\bmod64\); no input magnitude or unbounded quotient information remains. This proves the proposed modulus-64 periodicity for all \(x\ge8,y\ge12\).

For complete explicit evaluation, define \(H(s,t)\) by the above candidate equations at the harmless representative
\[
S=256+s,\qquad y=64+t,\qquad x=S-y
\quad(0\le s,t<64).
\]
For \(V\ge5\) set \(H=1\). Otherwise set \(H=1\) exactly when at least one displayed candidate satisfies the image-lemma Boolean test
\[
K\equiv0\pmod2\quad\lor\quad(A+K)\bmod4\in\{0,3\}.
\]
This is a finite, directly evaluable definition with no call to a Turing-machine simulator. The companion [pure-integer residue certificate](../im-results/agent34-c-degree-profile/two_step_density.py) evaluates all 4096 cells; its source is short enough for independent inspection.

The exact certificate census, grouped by \(V\) with \(V\ge5\) amalgamated, is:

| \(V\) | Total residue cells | \(H=1\) | \(H=0\) |
|---:|---:|---:|---:|
| 1 | 2048 | 768 | 1280 |
| 2 | 1024 | 768 | 256 |
| 3 | 512 | 416 | 96 |
| 4 | 256 | 240 | 16 |
| \(\ge5\) | 256 | 256 | 0 |
| **Total** | **4096** | **2448** | **1648** |

These integer counts can alternatively be verified by hand using \(S\bmod64\) rows. Every pair \((S\bmod64,y\bmod64)\) occurs with asymptotically equal frequency in the growing rectangles. Removing the finitely many coordinate boundary rows \(x<8\) or \(y<12\) costs \(O(N)\) points, hence does not alter the limiting fraction. This completes Theorem 1.

## Validation, significance, and limitations

The [companion independent exact-source script](../im-results/agent34-c-degree-profile/check_degree.py) evaluates the original recursive \`bounce\` and \`secNext\` branches and reconstructs inverse candidates. The residue-certificate script additionally compares the modular decision to a separately computed exact two-step existence test for **1,028,192** targets with \(8\le x<1024,\ 12\le y<1024\), plus **100,000** seeded large-coordinate targets. All comparisons passed locally with Lean 4.36.0-rc2 available for further formalization. Modulus-64 cells were also reproduced on explicit large-coordinate grids of periods 64,128,256,512,1024 and 2048; every tested period gave exactly \(153/256\) two-step hit density.

This theorem unconditionally forbids 40.234375% of all large pairs as outputs of two arbitrary source transitions. It is stronger than the previously derived 25% one-step missing-image density. It does **not** prove that a forbidden pair lies on the relevant Machine C halting locus and evades existing source-certified blank restrictions. Neither a global root invariant nor a Busy Beaver upper bound follows automatically. A source-connected Lean proof of the finite modular theorem is the next certification step; using the two-step test to exclude a full surviving blank halting family is the next genuine-root research step.
