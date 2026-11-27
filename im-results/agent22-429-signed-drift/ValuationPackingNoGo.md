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

## Kernel-checked cyclic backward uniqueness and exact signed-block bridge

Two further source-independent Lean 4.36.0-rc2 modules narrow the nonperiodic proof gap.

[ValuationPrimitive.lean](ValuationPrimitive.lean) proves backwards_unique: an integer-indexed sequence obeying 4^j v_next = v + K with 0<3v<K has unique backward history. Thus if two source values agree, all preceding gap lengths and values agree. It formalizes BackwardPrimitive, which says that the preceding n-gap windows at two distinct positions in a length-n word differ somewhere. It then proves window_source_injective and the full no_primitive_window contradiction against K<=6sum(j) in this abstract model. These claims use only standard Lean axioms; they do not yet prove that a usual primitive periodic word implies BackwardPrimitive, nor construct the integer-indexed slope sequence from the authentic signed source.

[SignedPairMacroBridge.lean](SignedPairMacroBridge.lean) formalizes the actual compressed signed F, EF, SF equations (including modular guards and every standalone F transition). Its theorem pairRun_model proves an E/S pair followed by 2(j-1) standalone Fs satisfies the exact half-rank step 4^j u_out = u_in + r_in + c and r_out = r_in + 3j + a, with (c,a)=(4,2) for E and (10,4) for S. The stronger pairRun_model_exists constructs the integer output half-rank automatically using fRun_parity and pairRun_output_even. This is an exact coordinate/guard bridge to [PeriodicMacroTransfer.lean](PeriodicMacroTransfer.lean). It is not yet imported directly into the archived SignedDrift source nor the authentic BB429 root model.

The subsequent [ValuationCyclic.lean](ValuationCyclic.lean) closes the previously missing standard cyclic-primitivity implication in Lean: any n-periodic gap sequence with minimal positive period n satisfies BackwardPrimitive. Its theorem no_primitive_periodic_slope combines this with the checked finite valuation budget to rule out every integer-indexed fixed-K legal slope path whose primitive gap schedule satisfies K<=6sum(j). The axiom printout contains only propext, Classical.choice, and Quot.sound. The subsequent [WeakCone.lean](WeakCone.lean) proves the boundary-dichotomy missing from the initial signed slope transfer: even when only 3v<=K is known, an equality phase forces an all-j=1 backward ray and thus an all-j=1 periodic word. Therefore a primitive periodic path with any genuine F-run must satisfy the strict cone automatically, and theorem no_primitive_periodic_weak_cone closes the entire normalized weak-cone contradiction in Lean. The **remaining formal gap is constructing that slope path and budget from the original SignedDrift and authenticated BB429 inverse source**.

Both files were actually compiled locally with no sorryAx; the first depends only on ValuationEdges, the second only on PeriodicMacroTransfer. They are ready for source integration and for resolving the remaining pure gap-periodicity bridge. These checked pieces do not decide the machine.
