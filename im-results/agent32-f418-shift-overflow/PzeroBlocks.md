# Exact F418 maximal p=0 blocks and their fatal endpoint language

**Scope:** a structural theorem about arbitrary safe pure checkpoints; no root-orbit verdict. The arithmetic and finite-word results are kernel-checked locally in Lean 4.36.0-rc2 using only standard axioms. The event adapter is type-checked locally against the original interfaces; full original-source check is queued in [CI 45784130107](https://github.com/FlareZ123/bb6/actions/runs/45784130107).

Let `pure(N,W)` mean the original shift2(N,1,2^W,W+1) checkpoint, with 0<N<2^W. Assume W>=3. A p=0 normal return occurs exactly when N is odd. Write M=N+7. Its exact update is M'=M/2+2^(W+2), W'=W+3. Factor M=2^l*u with u odd. Then l<=W (since M<2^(W+1)).

For 0<=j<=l, the j-th augmented register is

    M_j = 2^(l-j)*u + 2^(W-j+3)*P_j,
    P_j = 1+16+...+16^(j-1), P_0=0.

All M_j for j<l are even, M_l is odd. Thus l is exactly the length of this p=0 block. The normal-return proof composes 2j exact original arithmetic events to reach pure(M_j-7,W+3j).

## Classification for l>=2

An odd-only endpoint (all set bits at odd indices) exists **only** in either of the following two cases, and both cases are sufficient when the input is safe:

1. **Nonborrow:** W=l+2m, u=7+Q, where Q consists of m base-four digits in {0,2}. Equivalently N=2^l*(7+lowWord(v,m))-7 with 0<=v<2^m.
2. **Borrow:** u=1 and W=l>=3, i.e. N=2^W-7.

In both cases the endpoint satisfies the original OddChain(N_l,3), so its final relative valuation is 3, and it reaches the fatal shift1 event. **A maximal p=0 block of length at least 2 cannot terminate in a recoverable odd-only checkpoint.**

Proof: let a=W-l+3>=3. In the first case Q=u-7 satisfies Q<2^(W-l) from input width. The endpoint is 2^a P_l + Q, without carry or overlap. Bit a is set, so a must be odd; all even bits of Q vanish. This gives the stated unique base-four expansion. The high pulses have separation exactly four, so an odd-chain representation ends at relative valuation 3. Prepending arbitrary base-four digits 0 or 2 preserves that final valuation. In the second case d=7-u belongs to {2,4,6}; the endpoint is 2^(a+4)P_(l-1)+(2^a-d). The first surviving pulse forces odd a. If a>=5, bit a-1 of the remainder is set (even), contradiction. Thus a=3. The only odd-only remainder is 2, i.e. d=6. The resulting endpoint 2+128 P_(l-1) again has a high pair separated by four because l>=3.

## Explicit family size

For every l>=2 and m>=3, W=l+2m, all 2^m prepared inputs indexed by v in [0,2^m) are positive, satisfy N<2^W, are pairwise distinct, execute exactly l p=0 returns, and reach OddChain(...,3). The width proof uses 3*lowWord(v,m)+2<=2*4^m; injectivity uses the base-four expansion. Thus these are genuine halting prepared checkpoints, not simulations or probabilistic claims. For m<3, filter by safe input width; the classification still holds.

## Files and exact scope

- [F418PzeroBlock.lean](F418PzeroBlock.lean): replay formula, parity, constructor-level OddChain theorem, prepared family safety/injectivity.
- [F418PzeroGate.lean](F418PzeroGate.lean): noEven base-four encoding, nonborrow and borrow classification, exact length bound and terminal_oddchain. All compiled locally; audit axioms are propext, Classical.choice, Quot.sound only.
- [F418PzeroSource.lean](F418PzeroSource.lean): connects the above to original Prefix.normal_return_exact, EventSystem.safe_iterate and fatal_episode. CI checks original dependency objects and prints axiom audit; local interface harness is not claimed to establish original-source acceptance.
- Original source-connected root is (268311341,29); reachability of any of these prepared checkpoints from that root remains open.

This reduces the remaining reachability task: recoverable gates after a normal run must occur after a nonzero-p return or a singleton p=0 block, while fatal gates after long p=0 blocks have an exact regular-language inverse. No amount of counting prepared inputs decides the actual root orbit.
