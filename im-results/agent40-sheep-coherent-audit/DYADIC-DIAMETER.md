# Exact generic dyadic diameter of the Sheep first-even quotient

**Agent 40, 6 November 2026.** For every integer \(p\ge1\), the directed diameter of the **synthetic generic** Sheep first-even return graph \(G_p\) modulo \(2^p\) is exactly

\[
\boxed{\operatorname{diam}(G_p)=\lfloor p/2\rfloor.}
\]

This proves the all-parameter conjecture recorded in [the previous finite census](DIAMETER-FINITE.md), and sharpens the earlier free-start coherent-orbit theorem to the **same exact diameter** for pure dyadic moduli. An individual coherent witness uses one starting integer and consecutive genuine generic returns; its starting integer may depend on both residues. It combines a new target-saturation lemma with Agent 22's published-in-repository inverse-word bijection, CRT edge-realizability and outgoing-zero-hub results, and Agent 40's earlier exact shortest-to-zero theorem. It has a rigorous mathematical argument and independent Lean verification of its abstract affine core; an end-to-end original-machine Lean certificate is **not** claimed. The result concerns a **synthetic quotient graph**, with different positive integer witnesses allowed for different edges. It is not a genuine blank-orbit reachability theorem, does not close the Sheep holdout, and does not determine BB(6).

## Precise graph, original semantic boundary, and dependencies

The original Sheep machine is `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE`. Agent 16's [original-source even-section bridge](../agent16-sheep-even-return/README.md), [successful CI 41505950547](https://github.com/FlareZ123/bb6/actions/runs/41505950547), reduces its halting to the genuine even-section orbit from the fixed state \(10\) reaching a power \(2^j\), \(j\ge2\). Our graph \(G_p\), defined in [Agent 22's dyadic theorem](../agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md), has one vertex for each even residue modulo \(M=2^p\). An edge \(r\to s\) exists when a **legal, positive generic first-even section return** maps some source with residue \(r\) to a target with residue \(s\). A quotient path need not lift to a single physical orbit.

For \(1\le a<p\) and \(0\le h<p-a\), set \(c=a+h+1\), \(D_a=1+2^{a+1}\). Agent 22's source-realizable inverse-residue map is

\[
T_{p,a,h}(s)\equiv
2^aD_a^{-1}\bigl(3-2a+2^{h+1}3^{-h}(s-1)\bigr)\pmod {2^p}.
\tag{1}
\]

The inverses of the odd integers \(D_a,3\) exist modulo powers of two. For **every even** target \(s\), \(T_{p,a,h}(s)\to s\) is a genuine generic quotient edge, witnessed by arbitrarily large positive inputs via Agent 22's CRT construction.

The same earlier work proves a bijection between even residues \(r\) and admissible words \(W=((a_1,h_1),\ldots,(a_j,h_j))\) of total cost

\[
C(W)=\sum_{i=1}^{j}(a_i+h_i+1)\le p,
\]

whose inverse nesting from zero is \(r=\Phi_p(W;0)\), where

\[
\Phi_p(W;s)=T_{p,a_1,h_1}(\cdots T_{p,a_j,h_j}(s)\cdots).
\]

Write \(\lambda_p(r)=j\). Each letter costs at least two, hence \(\lambda_p(r)\le k:=\lfloor p/2\rfloor\). Agent 40's earlier [all-parameter shortest-to-zero argument](DYADIC-DISTANCE.md) establishes \(d_{G_p}(r,0)=\lambda_p(r)\) and shows the maximum code length is \(k\). The established zero hub gives one edge \(0\to s\) for every even \(s\).

## New saturation lemma

**Lemma.** For any admissible word \(W\) with \(C(W)\ge p-1\), and any even residues \(s,t\),

\[
\Phi_p(W;s)\equiv\Phi_p(W;t)\pmod {2^p}.
\tag{2}
\]

**Proof.** Formula (1) has the modular affine form
\[
T_{p,a,h}(s)\equiv b_{a,h}+2^c u_{a,h}s\pmod {2^p},
\qquad u_{a,h}=D_a^{-1}3^{-h}\ \text{odd}.
\]
Composing these affine maps multiplies all input differences by the product of their slopes. Thus
\[
\Phi_p(W;s)-\Phi_p(W;t)
\equiv 2^{C(W)}U_W(s-t)\pmod {2^p},
\]
where \(U_W\) is odd. Since both \(s,t\) are even, \(2\mid(s-t)\). Together with \(C(W)+1\ge p\), this makes the right side divisible by \(2^p\). QED.

The standalone [AffineSaturation.lean](AffineSaturation.lean) proves the affine-composition shift identity for arbitrary gate biases, factors, and costs, followed by the general even-target saturation statement for every \(p\le C+1\). It was compiled locally under Lean 4.36.0-rc2, and both theorems report **only** `[propext]` as an axiom, with no `sorryAx`. This certificate isolates the new arithmetic core; it does not itself import (1) or Agent 22's word-bijection proof.

## Exact diameter theorem

Fix \(p\ge1\), put \(k=\lfloor p/2\rfloor\), and let \(r,s\) be arbitrary even residue vertices.

1. If \(\lambda_p(r)<k\), take the canonical path \(r\to0\) of \(\lambda_p(r)\) generic edges, then the zero-hub edge \(0\to s\). This has length at most \(k\).
2. If \(\lambda_p(r)=k\), let \(W\) be the canonical word of \(r\). Its \(k\) letters give \(C(W)\ge 2k\ge p-1\). Saturation yields \(\Phi_p(W;s)=\Phi_p(W;0)=r\). Apply the letters of \(W\) in reverse order starting at the chosen target \(s\). The intermediate residues are even and every inverse letter represents a genuine generic quotient edge; reading these backwards gives a **\(k\)-edge directed path from \(r\) to \(s\)**.

The upper bound holds for all pairs. For \(p=1\), the only vertex is zero and the diameter is zero. The shortest-to-zero theorem supplies an \(r\) at distance exactly \(k\) from zero, giving the matching lower bound. Therefore \(\operatorname{diam}(G_p)=k\). QED.

**Stronger constructive corollary:** Any residue whose canonical word has \(C(W)\ge p-1\) reaches every even target within \(\lambda_p(r)\) quotient edges using the **same sequence of inverse letters**. The integer witnesses remain independently chosen for each edge.


## Stronger theorem: exact coherent free-start diameter

For even residue vertices \(r,s\pmod {2^p}\), define \(d_p^{\mathrm{coh}}(r,s)\) as the smallest number of **consecutive actual generic first-even Sheep returns** in one valid positive integer trajectory \(x,E(x),\ldots,E^j(x)\), where the **freely chosen** starting integer \(x\) is congruent to \(r\), and the final integer to \(s\), modulo \(2^p\). Each first-even block is required to have the normal odd-cofactor generic branch. The zero-length path is allowed when the residues coincide.

**Theorem.** For every \(p\ge1\),
\[
\boxed{\max_{r,s\text{ even}}d_p^{\mathrm{coh}}(r,s)=\lfloor p/2\rfloor.}
\]
The minimum is attained by legal positive integer starts, which can be chosen arbitrarily large. This strengthens Agent 22's [coherent single-orbit theorem](../agent22-sheep-mixed-hub/COHERENT-ORBIT.md), whose general mixed-modulus upper bound is \(\lfloor p/2\rfloor+1\).

**Lemma (coherent lifting of any prescribed inverse word).** Let \(W\) be admissible modulo \(2^p\), with cost \(C\le p\), and let \(s\) be any even target residue. Put \(P=p+C\). Every sufficiently large positive integer
\[
x\equiv \Phi_P(W;s)\pmod {2^P}
\]
executes **exactly the consecutive generic first-even branch letters of \(W\)**, and the endpoint has residue \(s\pmod {2^p}\).

To prove this, at a letter \((a,h)\), write \(x=2^a u\) with \(u\) odd. The exact generic section formula gives
\[
2(F(x)-1)=(1+2^{a+1})u+2a-3.
\]
The defining inverse congruence (1) says
\[
(1+2^{a+1})u+2a-3
\equiv 2^{h+1}3^{-h}(s'-1)\pmod {2^{\ell-a}}
\]
for its next target residue \(s'\), where \(\ell\) is the presently retained precision. Since \(s'\) is even and \(\ell\ge a+h+2\), the left side has **exact valuation \(h+1\)**. It follows that \(v_2(F(x)-1)=h\); the return block is the prescribed branch, and its output \(E(x)=1+3^h(F(x)-1)/2^h\) is \(s'\) modulo \(2^{\ell-(a+h+1)}\). The source has exact valuation \(a\) because (1) is \(2^a\) times an odd residue. Inductively, at stage \(i\), the retained precision is \(P-\sum_{m<i}c_m=p+\sum_{m\ge i}c_m\ge c_i+1\). This proves the complete word and final target congruence. Choosing the initial representative sufficiently large makes the finitely many required odd cofactors at least five and all intermediate numbers positive. The prescribed affine returns have positive slopes, so the guards remain satisfied for all sufficiently large representatives in this congruence class.

**Case 1: maximal words.** If the canonical word \(W\) of \(r\) has length \(k=\lfloor p/2\rfloor\), then \(C(W)\ge p-1\). Saturation gives \(\Phi_p(W;s)=\Phi_p(W;0)=r\) for **every** even target \(s\). Coherent lifting gives an actual \(k\)-return trajectory starting at \(r\) modulo \(2^p\) and ending at \(s\). There is no extra hub step.

**Case 2: shorter words.** Suppose the canonical word \(W\) of \(r\) has length \(j<k\). Coherently lift it with terminal residue zero. Let the resulting sufficiently large start be \(x_0\), and let \(y_0=E^j(x_0)\equiv0\pmod {2^p}\). Define
\[
L=2^{p+C(W)},\qquad
A=\prod_{i=1}^j 3^{h_i}(1+2^{a_i+1}),
\]
where \(A\) is positive and odd (empty product \(1\)). The corrected exact affine formula for the generic return,
\[
E(x)=\frac{3^h(1+2^{a+1})x+
2^a[2^{h+1}+3^h(2a-3)]}{2^{a+h+1}},
\]
and the guaranteed same branch itinerary imply, for all sufficiently large \(N\),
\[
E^j(x_0+LN)=y_0+A\,2^pN.
\]
Set \(b=y_0/2^p\). Since \(A\) is odd, choose a nonnegative sufficiently large \(N\) solving
\[
b+AN\equiv1+2(s-p)\pmod {2^{p+1}}.
\]
Then the intermediate endpoint \(y=2^p u\) has **exact** valuation \(p\), odd factor \(u\ge5\), and
\[
F(y)=2^pu+p+(u-1)/2\equiv s\pmod {2^p}.
\]
Because \(s\) is even, \(F(y)\) is even, so \(E(y)=F(y)\) gives one final *genuine generic first-even return*. This realizes \(r\to s\) by \(j+1\le k\) consecutive returns in the **same** positive integer orbit.

For \(p=1\), there is only one even residue, with distance zero. Thus the coherent upper diameter is \(k\) for every \(p\). Every coherent path projects to a valid synthetic path, so the previous shortest-to-zero lower bound \(k\) applies unchanged. QED.

**Essential boundary:** These starts are constructed by modular lifting and generally enormous. They are **not** the authentic fixed blank entry \(10\). The theorem does not imply that the true Sheep orbit visits a chosen residue, let alone that it halts.

## Reproduction, novelty, and remaining task

The independent [coherent_diameter_certificate.py](coherent_diameter_certificate.py) checks 324,039 maximal-shell and 84,366 shorter-shell single-orbit examples with exact branch valuations; [diameter_certificate.py](diameter_certificate.py) reconstructs the inverse map and canonical decoder from the displayed arithmetic and exhaustively checks **every even target for every maximal-code source** for \(1\le p\le15\). The earlier [independent complete graph BFS](DIAMETER-FINITE.md) verified the entire all-pairs diameter for \(p\le11\). Neither finite computation supplies the proof's all-parameter quantifiers.

The precise scope of this advancement is a synthetic graph-theoretic theorem, building on documented all-parameter **mathematical** prerequisites. The kernel verifies the new algebraic saturation abstraction; a complete Lean proof of the actual inverse-word bijection and its original-machine transport remains open. External academic novelty has not been established. Keep this note under `im-results/`, not `results/`. The authentic Sheep holdout still requires a global invariant or real witness for the **single** even orbit from \(10\).
