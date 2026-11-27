# #429: exact finite valuation packing and reverse uniqueness

**Status:** locally Lean-certified arithmetic results for the abstract signed half-rank model. They are not original-source nonhalting proofs and do not decide #429 or BB(6).

## The exact counting result

For fixed positive integer K, consider witnesses with 0 < 3v < K, k >= 1, and 4^k z = v + K. The quotient z lies in (0,K/12) union (K/4,K/3): for k=1 it lies in the second interval, for k>=2 in the first. Moreover z determines both v and k uniquely, since K < v+K < 4K/3 and two different powers of 4 have ratio at least four. Both statements are Lean-checked in ValuationPacking.lean.

The all-denominator grid theorem in PeriodicGridPacking.lean proves that these two intervals contain at most floor((K-1)/6) distinct integer points. Therefore the number of distinct valuation pairs (v,k) with 4^k dividing v+K and 0<3v<K is at most floor((K-1)/6). This does not require parity, reduced denominators, or a machine orbit. The complete finite-pair injection and counting result is theorem ValuationPacking.finite_valuation_packing_pairs.

## The full all-exponent family bound

For a finite family of distinct source values v_i, exponents j_i >= 1, and successors w_i such that
\[
0<3v_i<K,\qquad 4^{j_i}w_i=v_i+K,
\]
every s=1,...,j_i gives another valid quotient z_{i,s}=4^{j_i-s}w_i. These distinct pairs (v_i,s) are all injectively mapped to grid points. Thus
\[
\boxed{\sum_i j_i\le\left\lfloor(K-1)/6\right\rfloor.}
\]
This is theorem ValuationPacking.edge_family_budget in ValuationEdges.lean, locally compiled with Lean 4.36.0-rc2 and only [propext, Classical.choice, Quot.sound]. Theorems equal_successor_forces_equal_parameters and no_distinct_edge_budget likewise compiled with standard axioms. No sorryAx.

## Application to signed periodic and finite triple-repeat paths

The signed macro slope recurrence is
\[
4^{j_i}v_{i+1}=v_i+K,\qquad 0<3v_i<K.
\]
For a primitive cyclic j-gap word, the sources v_i are pairwise distinct. If v_r=v_s at distinct positions, the two preceding edges have equal successor quotients. The certified reverse-uniqueness lemma forces equal previous sources and equal previous j exponents. Iterating backwards around the cycle forces the entire j-word invariant under nontrivial shift s-r, contradicting its primitive period. This argument does **not** need K odd or any rational radix-four expansion.

Consequently, with t=sum j_i for a primitive gap period, the finite-family budget gives K>=6t+1. The exact signed E/S type rank budget gives K<=6t, contradiction. This shortens the [all-period no-go](PeriodicRunNoGo.md) and [finite triple-repeat no-go](FiniteTripleNoGo.md), and isolates one finite cyclic backward-primitivity composition as a missing Lean link.

**Scope:** The reverse-uniqueness, complete finite exponent budget, and abstract rank-budget contradiction are all checked in Lean. The cyclic backward-primitivity bridge and original source SignedDrift F/EF/SF connection have not been jointly kernel-checked. The resulting all-period and finite triple-repeat conclusions remain paper-level, not whole-machine decisions. Aperiodic inverse paths remain open.

## Reproduction

Compile PeriodicGridPacking.lean first with -o, then ValuationPacking.lean with -o, then ValuationEdges.lean, setting LEAN_PATH to their containing directory. All three use only Lean 4.36.0-rc2 and Std.
