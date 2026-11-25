# Machine C: Haar-null ordinary ancestry and asymptotically exhaustive dyadic residue sieves

**Theorem.** There is a sound finite binary congruence sieve for the authentic blank-origin Machine C section map whose surviving parameter density tends uniformly to zero on the entire high-stopping family, and tends to zero on the low-stopping family. The result is about necessary conditions in density, not pointwise exclusion. No Machine C decision or BB(6) value follows.

The algebraic identities and arbitrary collision construction are kernel-checked in [DyadicAncestry.lean](../im-results/agent12-c-high-shadow/DyadicAncestry.lean) and the generic closure theorem in [DyadicAncestryBridge.lean](../im-results/agent12-c-high-shadow/DyadicAncestryBridge.lean), with Lean 4.36.0-rc2 and standard axioms. The original-source adapter is [DyadicAncestrySource.lean](../im-results/agent12-c-high-shadow/DyadicAncestrySource.lean). The measure-theoretic argument below is a written proof, not a formalization of Haar measure.

## 1. Exact affine coordinates

Use the established exact section map BB6.Agent46.secNext, blank entry (5,1), and define

    M=a+2k, o=a mod 2, L=(a+2+o)/2, H=(M-o)/2.
    a=2L-2-o, M=2H+o, k=H-L+1+o, a+k=L+H-1.

The complete high-right predecessor theorem complete_section_inverse (restated as RawParent in PurePowerRawParent.lean) implies every successful section edge is either:
* an ordinary edge of positive shift r with M'=M+3r+1 and 2^r(a+2+o)=2a'+2k'+2o (direct r=1; regular bounce r=n+2);
* a small-right output k'<8;
* an exceptional zero/one-input output with a'+k'=2^n or a'+k'+1=2^n.

The alternatives need not be disjoint. Ignoring positivity and region guards gives an overapproximation. Extend the ordinary maps to X=Z_2^2 × {0,1}, normalized Haar probability and equal parity masses:

    o'=(o+r+1) mod 2,
    d_r(o)=(o+3r+1-o')/2,
    H'=H+d_r(o), L'=2^r L-H'+1-o.                 (1)

Each f_r is an injective clopen embedding scaling measure by 2^(-r). For a chronological nonempty word w with sum R,

    H'=H+D_w(o), o'=o_w(o),
    L'=2^R L-Q_w H'+C_w(o),                       (2)

where Q_w is odd, because the final edge contributes 1 and all earlier terms are multiplied by an even power. The parity map is a permutation. The Lean theorems affine_of_equations, run_formula and coeff_q_odd check these facts algebraically.

## 2. Critical ancestry and stationarity

Set S_0=X, S_(n+1)=union_r f_r(S_n) for r>=1. These are decreasing measurable sets, exactly the unrestricted ordinary word images of depth n. Let S=intersection_n S_n and delta=mu(S). The weights sum_r 2^(-r)=1. We have S=union_r f_r(S) up to a null set: the forward inclusion union_r f_r(S) subset S is immediate. For fixed B the difference between S_(n+1) and union_{r<=B} f_r(S_n) has measure at most 2^(-B). Passing to decreasing intersections (finite union commutes with these nested intersections; each f_r is injective) gives mu(S minus union_r f_r(S))<=2^(-B) for every B. Consequently

    mu(union_r f_r(S))=delta=sum_r mu(f_r(S)).

All images f_r(S) are pairwise disjoint modulo null sets.

Write s_o(H) for the measure of the L-fiber of S. Fubini and the disjointness give s=sum_r p_r s∘T_r^(-1), with p_r=2^(-r) and T_r(H,o)=(H+d_r(o),o'). The T_r are measure-preserving bijections. Since s is bounded, in L² we have

    sum_r p_r ||s-s∘T_r^(-1)||²
      =2||s||²-2⟨s,sum_r p_r s∘T_r^(-1)⟩=0.

Thus s is invariant under each T_r. T_1 and T_3 preserve parity and translate H by 2 and 5, generating addition by 1. An L² function invariant under adding 1 on Z_2 is constant almost everywhere: its averages over every finite binary residue partition are constant by cyclic permutation, and those conditional expectations converge in L² by density of cylinder functions. T_2 interchanges parities, so both constants equal delta. Almost every mass/parity fiber has measure delta.

## 3. Arbitrary multiplicity collisions

For any positive N take p_1=1, p_(i+1)=p_i+2^(p_i+1), R=p_N+1, q_i=R-p_i. Both shifts p_i,q_i are positive odd, and p_N-p_i is divisible by 2^(p_i+1) by summing the recurrence. The N two-edge words (p_i,q_i) preserve parity and have common mass translation D=(3R+2)/2. From (1),

    L'=2^R L-2^q_i(H'-d_(q_i)(o)-1+o)-H'+1-o.

Because q_i=1+(p_N-p_i), d_(q_i)(o)=2+3(p_N-p_i)/2=2 mod 2^p_i. Restrict H' to the positive-measure cylinder H'=3-o mod 2^p_N. Each word image then lies in exactly the same L-cylinder L'=-H'+1-o mod 2^R.

At almost every H' there the input fiber H'-D has measure delta, common to all words. Their image fibers each have measure 2^(-R) delta, and are pairwise disjoint modulo null sets, because their last shifts q_i are distinct and f_(p_i)(S) subset S. The containing cylinder has measure 2^(-R), so N delta<=1. Arbitrary N implies delta=0.

**Theorem 1.** The infinite ordinary ancestry set S is Haar-null, and mu(S_n) tends to zero.

Theorems many_splits, splitPos_div and splitPos_succ_gt check the arbitrary-length collision construction. The positions start 1,5,69; this proof supplies no practical rate.

## 4. Uniform smallness of mass fibers

Let s_n be the fiber measure of S_n, and P u=sum_r p_r u∘T_r^(-1). The union bound gives s_(n+1)<=P s_n pointwise (all these finite-depth fibers are countable unions of clopen sets). For precision J the image of any r>=J lies in G_J, the two graph cylinders L+H-1=0 or L+H=0 modulo 2^J, both parities allowed. The fiber bound of G_J is 2^(1-J).

Define V_(n,J) as the finite union of all length-n word images with shifts <J, plus images of G_J under all words of length <n with shifts <J. The most recent large shift shows S_n subset V_(n,J). The extra fiber measure is at most n*2^(1-J), since the sum of contraction weights of all words of each fixed length is 1. V_(n,J) is clopen.

For epsilon>0 choose n_0 with mu(S_(n_0))<epsilon/4 and then J so V=V_(n_0,J) has mu(V)<epsilon/2. Its fiber function u depends on a finite residue partition of the mass/parity space. P preserves functions on that partition and is doubly stochastic and irreducible there (T_1, T_3 generate translations, T_2 connects parities). Cesaro averages of P^t u converge uniformly to the constant mu(V): every subsequential limit is fixed by P by telescoping, the maximum principle gives constancy, and the mean is preserved. Since s_n decreases, s_(n_0+T)<=P^t u for all 0<=t<=T, hence is bounded by their Cesaro average. For large T its supremum is <epsilon. Another finite clopen overapproximation V_(n,J') increases this fiber bound by at most n*2^(1-J').

**Theorem 2.** For every eta>0 there is a finite n and a clopen binary-residue set V containing S_n whose L-fiber measure is at most eta for every H and parity.

## 5. Uniform sparsity on even-slope affine lines

Fix a parity and either parametrization (L,H)=(l0+u,h0+alpha*u) or (l0+alpha*u,h0+u), alpha even, u in Z_2. Take V from Theorem 2 of precision K, fiber bound eta, and a nonempty word w of length at least K, total shift R>=K. Inverting (2) requires L'+Q_w H'-C_w=0 modulo 2^R. The coefficient of u is 1+Q_w alpha or alpha+Q_w, respectively odd. Exactly one u residue class modulo 2^R is admissible. On writing u=u0+2^R v, the input L is an odd-affine function of v while input H is fixed modulo 2^K. Thus the measure of v satisfying V is at most eta. The word image f_w(V) has slice measure at most 2^(-R) eta. Summing over all words of length K gives eta, because their contraction weights sum to 1 and S_(n+K) is contained in their images of V.

**Theorem 3.** The measures of S_n on both even-slope line types tend uniformly to zero, over all offsets, even slopes and fixed parities.

## 6. Finite congruence closures including every exception

For J>=1 let E_J be the clopen birth set with any of:
* H-L+1+o congruent to 0,...,7 modulo 2^J;
* L+H-1 or L+H congruent to 0,1,2,4,...,2^(J-1) modulo 2^J.

This contains the root, every actual exceptional source output, and every image with r>=J. E_K subset E_J when K>=J. On every mass fiber and every even-slope line its parameter measure is at most (2J+10)2^(-J): each birth form has odd parameter coefficient.

Define P_K to be the least set of residue triples modulo 2^K in L,H and exact parity containing E_K and closed under f_r modulo 2^K for 1<=r<K. This is computable by finite BFS. By the exact source classification, the root and every genuine blank-origin section state are admitted. Long shifts are covered by E_K itself. The generic Lean theorem sieve_sound checks precisely this closure implication.

For fixed n,J let U_(n,J) be the finite union of length-n word images with all shifts <J, plus images of E_J under words of length <n with all shifts <J. This clopen set depends on some finite precision K_0>=J. Every ordinary path from E_J has endpoint in U: either its last n shifts are small, or the most recent large shift lands in E_J, or the path is shorter than n. For K>=K_0 any BFS path from E_K lifts to an ordinary path in Z_2 from an arbitrary representative of its initial residue, since the affine maps commute with reduction. Its endpoint is in U, and membership in U depends on precision K_0. Therefore the whole 2-adic lift of P_K lies in U.

For either line type, a nonempty word image f_w(E_J) has slice measure at most 2^(-R)(2J+10)2^(-J): the inverse parameterization as in section 5 makes input L have odd slope and input H even slope, so all birth forms have odd slope. The empty word has the same bound with R=0. Summing over short words, the length-n ordinary images being a subset of S_n, yields

    slice(U_(n,J)) <= slice(S_n)+n(2J+10)2^(-J).

First choose n by Theorem 3, then J large. This proves the main statement.

**Theorem 4 (uniform density completeness).** For every epsilon>0 some K_0 has the following property: for all K>=K_0, P_K admits at most an epsilon fraction of the 2^K parameter residues on every even-slope line of either type and either fixed parity. In particular its global residue density tends to zero. P_K is sound for every authentic blank-origin state. This includes exceptional births at arbitrary times, without assuming that the true orbit is eventually ordinary. The proof guarantees termination of a search over finite precisions for any positive tolerance, without an efficient complexity bound.

## 7. Authentic stopping families

The established source stopping criterion uses the high family a=2j+3, k+j+3m+5=2^(2m+2)(j+3), and the low family a=1, k=2^(2m+3)-(3m+4). In the new coordinates:

    high: L=j+3, H=2^(2m+2)L-3m-4, o=1;
    low:  L=2, H=k, o=1.

The high family for every fixed m is an even-slope line, so the admitted fraction of j modulo 2^K tends to zero **uniformly for every m**, including small m. In the low family, for 2m+3>=K we have H=-3m-4 modulo 2^K. Multiplication by odd 3 is invertible, so Theorem 4 on the vertical line L=2 bounds the surviving asymptotic fraction of low m indices. Finite smaller m do not affect the density.

Zero density is compatible with infinitely many surviving parameter values and with one authentic halting visit. This is not a pointwise halting decision. The earlier [semilinear obstruction](2026-11-24-machine-c-semilinear-obstruction-agent12.md) rules out fixed finite congruence terminal-free inductive invariants; this theorem instead proves convergence of necessary conditions in density.

## Reproducibility

The affine-coordinate and collision algebra, generic closure soundness, and original-source adapter are in the three linked Lean modules. The finite BFS demonstration is [dyadic_sieve.cpp](../im-results/agent12-c-high-shadow/dyadic_sieve.cpp), built with C++20; its large masks are computational experiments, not kernel-certified numerical counts. No numerical experiment is needed for the limiting density theorem.
