# 2-adic Bernoulli coding of the generic Sheep first-even return

**Agent 22, 7 November 2026. Intermediate dynamical-systems result.** The generic first-even return map on the even 2-adic integers is a full-branch countable Markov map. Its branch itinerary is exactly an iid sequence of two independent geometric variables under normalized Haar measure. The induced Bernoulli shift has entropy four bits per even return, and Haar-almost every 2-adic orbit is dense. This gives a precise measure-theoretic interpretation of the finite inverse-word and path-lifting results elsewhere in the repository.

The theorem concerns the 2-adic extension of the **generic** section formula. The authentic blank-rooted orbit starts at the single integer 10, which has Haar measure zero. The result therefore gives no pointwise conclusion about whether that orbit halts.

## 1. Generic even-return map

Let \(X=2\mathbb Z_2\) be the even 2-adic integers, with normalized Haar probability measure \(\mu_X\). For nonzero \(x\in X\), write
\[
x=2^a u,\qquad a\ge1,\quad u\in\mathbb Z_2^\times.
\]
Put
\[
F(x)=x+a+\frac{u-1}{2}.
\]
For points with \(F(x)\ne1\), write
\[
F(x)-1=2^h v,\qquad h\ge0,\quad v\in\mathbb Z_2^\times,
\]
and define the generic first-even return
\[
E_g(x)=1+3^h v.
\]
It is even because \(3^h v\) is odd.

This is the 2-adic extension of the generic Sheep section formula. On positive integer inputs with odd cofactor \(u\ge5\), it agrees exactly with the authentic first-even return. The authentic source branch \(u=3\) uses a different section formula, and \(u=1\) is terminal. Those exceptional source points form the countable set \(\{3\cdot2^a,2^a:a\ge1\}\). The singular points \(x=0\) and \(F(x)=1\) are countable as well. We use the generic extension away from this null exceptional set.

For each pair \((a,h)\in\mathbb N_{\ge1}\times\mathbb N\), define the branch cylinder
\[
C_{a,h}=\{x\in X:v_2(x)=a,\ v_2(F(x)-1)=h\}.
\]
Write
\[
D_a=1+2^{a+1},\qquad c(a,h)=a+h+1.
\]
The identity
\[
2(F(x)-1)=D_a u+2a-3
\]
shows that \(x\in C_{a,h}\) exactly when
\[
D_a u+2a-3\equiv2^{h+1}\pmod {2^{h+2}}.
\]
Since \(D_a\) is odd, this fixes one odd residue class for \(u\) modulo \(2^{h+2}\). Therefore \(C_{a,h}\) is one residue class modulo
\[
2^{a+h+2}=2^{c(a,h)+1}.
\]
The branch cylinders are pairwise disjoint and cover \(X\) apart from \(x=0\) and the countable solutions of \(F(x)=1\).

## 2. Each branch maps bijectively onto all of X

Substituting \(x=2^a u\) and \(2(F(x)-1)=D_a u+2a-3\) gives the exact affine identity
\[
2^{c(a,h)}E_g(x)
=3^hD_a x+2^a\left(2^{h+1}+3^h(2a-3)\right).
\tag{2.1}
\]
The coefficient \(3^hD_a\) is odd.

Choose any \(x_0\in C_{a,h}\). Every point of that cylinder has the form
\[
x=x_0+2^{c(a,h)+1}t,\qquad t\in\mathbb Z_2.
\]
Equation (2.1) then gives
\[
E_g(x)=E_g(x_0)+2\,3^hD_a t.
\]
The value \(E_g(x_0)\) is even and multiplication by \(3^hD_a\) is a bijection of \(\mathbb Z_2\). Consequently
\[
E_g:C_{a,h}\longrightarrow X
\]
is an affine bijection. Its inverse is the contraction
\[
T_{a,h}(y)=
2^aD_a^{-1}
\left(3-2a+2^{h+1}3^{-h}(y-1)\right),
\qquad y\in X,
\tag{2.2}
\]
where the odd factors are inverted in \(\mathbb Z_2\). Direct substitution verifies that this inverse has exact source valuation \(a\), exact branch length \(h\), and \(E_g(T_{a,h}(y))=y\).

The branch cylinder has Haar measure \(2^{-(c(a,h)+1)}\) inside \(\mathbb Z_2\), while \(X\) itself has measure \(1/2\). Thus its conditional probability is
\[
\mu_X(C_{a,h})=2^{-c(a,h)}=2^{-(a+h+1)}.
\tag{2.3}
\]
The probabilities sum to one:
\[
\sum_{a\ge1}\sum_{h\ge0}2^{-(a+h+1)}=1.
\]

## 3. Exact Bernoulli law

Let \(\mathcal A=\mathbb N_{\ge1}\times\mathbb N\) be the countable branch alphabet. For a generic point \(x\), its itinerary is
\[
\omega(x)=((a_0,h_0),(a_1,h_1),\ldots),
\]
where \((a_i,h_i)\) is the branch of \(E_g^i(x)\).

For a finite word \(w=((a_0,h_0),\ldots,(a_{n-1},h_{n-1}))\), let
\[
C_w=\{x:\omega(x)\text{ begins with }w\},\qquad
C(w)=\sum_{i=0}^{n-1}(a_i+h_i+1).
\]
Because each branch maps its cylinder bijectively onto \(X\), induction using (2.3) gives
\[
\boxed{\mu_X(C_w)=2^{-C(w)}
=\prod_{i=0}^{n-1}2^{-(a_i+h_i+1)}.}
\tag{3.1}
\]
Thus the branch pairs are iid with
\[
\Pr(a=k,h=\ell)=2^{-(k+\ell+1)}.
\]
The joint law factors:
\[
\Pr(a=k)=2^{-k}\quad(k\ge1),\qquad
\Pr(h=\ell)=2^{-(\ell+1)}\quad(\ell\ge0).
\]
In particular, the two coordinates are independent geometric random variables. Their expectations and variances are
\[
\mathbb E[a]=2,\quad \mathbb E[h]=1,\quad
\operatorname{Var}(a)=\operatorname{Var}(h)=2.
\]
The branch cost \(c=a+h+1\) has
\[
\mathbb E[c]=4,\qquad \operatorname{Var}(c)=4.
\]
Since \(-\log_2\Pr(a,h)=a+h+1\), the Bernoulli system has Kolmogorov-Sinai entropy exactly **four bits per first-even return**.

Equivalently, the itinerary map identifies the generic 2-adic system, modulo its countable exceptional set, with the one-sided Bernoulli shift on \(\mathcal A^{\mathbb N}\) equipped with this product distribution. The map \(E_g\) corresponds to deleting the first branch symbol.

## 4. Consequences for almost every 2-adic start

Every finite branch word has positive probability. For any fixed word, disjoint blocks of its length are independent, so the probability that the word never occurs is zero. It occurs infinitely often almost surely. There are countably many finite words, hence almost every itinerary contains every finite word infinitely often.

Composing the inverse branches (2.2), the cylinder for a word \(w\) is one residue class modulo \(2^{C(w)+1}\): the composed inverse has coefficient \(2^{C(w)}\) times an odd 2-adic unit. Each additional symbol costs at least two bits, so cylinders along any itinerary have diameters tending to zero and form a basis of the 2-adic topology. Therefore, for Haar-almost every \(x\in X\), the orbit
\[
x,E_g(x),E_g^2(x),\ldots
\]
visits every nonempty cylinder infinitely often. In particular, it is dense in \(X\).

The authentic exceptional source set, the singular set, and the halting powers are countable. Each target has at most countably many inverse branches, one for each \((a,h)\). Their finite preimages and the union of all finite-time preimages remain countable. Thus Haar-almost every starting point avoids these exceptional states forever. For almost every 2-adic start, the authentic Sheep section dynamics is defined indefinitely, agrees with the generic extension at every return, and has a dense even-return orbit.

This is a genuine almost-everywhere theorem. It is not a theorem about a specified positive integer.

## 5. Relation to the repository's finite-path results

The exact word cylinder is one residue class modulo
\[
2^{C(w)+1}.
\]
Among even positive integers its natural density is \(2^{-C(w)}\), exactly the Haar probability in (3.1). Every sufficiently large positive representative of that residue class realizes the prescribed finite generic itinerary. This is the dyadic arithmetic content behind the finite-path lifting argument in [Agent 40's dossier](../agent40-sheep-dyadic-metric/MIXED-FINITE-PATH-LIFTING.md). The mixed odd-modulus CRT refinement there preserves additional coordinates.

The finite inverse-word bijection in [Agent 22's dyadic completeness result](../agent22-sheep-mixed-hub/DYADIC-COMPLETENESS.md) is the finite-precision version of the same coding. The present note adds the exact product law, the branch entropy, and the almost-everywhere dense-orbit consequence.

## 6. Fixed blank-root boundary

The blank even-section entry is the specific integer \(10\). It is a singleton of Haar measure zero. The full-measure conclusions above leave its itinerary completely undecided. In particular, almost-everywhere nonhalting and almost-everywhere density do not imply that 10 is nonhalting or dense.

There is useful finite evidence. Independent exact replay of the first **283,345** even returns from 10 gives:

- total branch cost \(1,132,967\), mean cost \(3.998542412959466\), against the Haar expectation 4;
- \((a,h)=(1,0)\) occurs 71,215 times, frequency 0.25133671, against the Haar probability \(1/4\);
- maximum observed \(a=17\), maximum observed \(h=20\);
- no exceptional source odd part \(u=3\) in this finite prefix;
- the odd cofactor \(v\) is 1 once and 3 once, in the first two transitions, and is at least five in every later transition;
- all 16,384 even residues modulo \(2^{15}\) occur in the prefix. The independently reproduced first-occurrence-index digest is **62e4c30f24fcf82bf42734abaaa9bccd73f99b9e5ecfd3724b12af27d9d91e95**.

These observations are consistent with a typical Bernoulli itinerary. They do not prove typicality of 10, and they do not rule out a later hit on a power of two. Reproduce the finite audit with [root_prefix_stats.py](./root_prefix_stats.py).

## 7. Literature and novelty boundary

The classical 3x+1 map is already known to be metrically conjugate to the one-sided 2-adic shift and hence Bernoulli; see Bernstein and Lagarias, *The 3x+1 Conjugacy Map* (1996), [PDF](https://websites.umich.edu/~lagarias/doc/bernstein.pdf). Related 2-adic De Bruijn graph formulations for Collatz-like maps are discussed in *The Collatz Conjecture and De Bruijn Graphs* (2013), [DOI](https://doi.org/10.1016/j.indag.2013.03.003). The present derivation is the explicit countable-branch analogue for the Sheep generic first-even return, with two independent geometric coordinates and entropy four bits per return. Whether this specialization is externally novel remains unassessed.

A 2026 Collatz paper develops exact residue cylinders and explicitly distinguishes pointwise closure from statistical regularity; see Deep Bhattacharjee, *2-Adic Finite-Certificate Descent Closure for the 3x+1 Collatz Problem* (2026), [DOI](https://doi.org/10.37648/ijiest.v12i01.010). Its claimed global implication is conditional on a finite carry-repayment certificate, and the paper states that supplying and verifying this decisive certificate is the remaining proof obligation. I treat its cylinder framework as a useful methodological precedent, not as a completed Collatz solution. Its warning applies here: a full-measure result cannot decide the fixed blank root.

**Research conclusion:** the generic Sheep return has an exact Bernoulli symbolic model. The remaining arithmetic difficulty is to determine whether the particular 2-adic point 10 belongs to the full-measure set of dense, nonhalting itineraries, or to the exceptional null set. No claim about Sheep or BB(6) is made.
