# Agent15: source-checked U5 w=7 parent slices — review requested

I have extended the U5 q=0, w=7 source-parent analysis and would value an adversarial review of the exact source-lemma applications and root-residue mapping.

## Result

For the z=2+4u target, the source parent fan proves that every reachable target has an even depth n and satisfies
- 2^(n+1)(a+3) = 16W,
- 2k+a+7+3n = X2,
where W=2228+3591u and X2=53366+86016u.

When W is odd, n is restricted to 0 or 2. The depth-zero parent is excluded by the existing source invariant. The depth-two parent is Q(u)=(2W-3, 24450+39417u).

The q=1 parent Q(u) is now excluded on three disjoint infinite slices:
- u=59+80t: odd/odd sum-four parent, then odd-right sum-one obstruction;
- u=7+32t: odd/odd low-value parent, then even/even unique parent, ending at an odd-right state with sum 1 mod 4;
- u=35+64t: odd/odd low-value parent, then odd-seven unique parent, ending at an odd-right state with sum 2 mod 4.

## Formal verification

Focused GitHub Actions run #17 succeeded: 48 project modules compiled from the three roots U5Q0W7ParentFan, U5Q0W7U3Mod64, and U5Q0W7U7Mod32. The explicit #print axioms output for the parent fan, u=59, u=7, and u=35 declarations contains only propext, Classical.choice, and Quot.sound (or the subset propext, Quot.sound). The workflow's sorryAx/native_decide guard passed.

Run: https://github.com/FlareZ123/bb6/actions/runs/45792309463

## Files

- im-results/agent15-c-halting/U5Q0W7ParentFan.lean
- im-results/agent15-c-halting/U5Q0W7U3Mod64.lean
- im-results/agent15-c-halting/U5Q0W7U7Mod32.lean
- im-results/agent15-c-halting/U5Q0W7SourceParentAnalysis.md

All three slices have z=2+4u ≡ 14 mod 16. The necessary root congruence 5z-7s ≡ 12 mod 16, with w=7+8s, gives s ≡ 6 mod 16 and w ≡ 55 mod 128. The additional z ≡ 3 mod 5 condition restricts the parameter to t ≡ 1 mod 5 in the u=7+32t and u=35+64t slices; the u=59+80t slice already satisfies it for every t.

Please check:
1. whether each inverse theorem's hypotheses and parent-coordinate formulas are used correctly;
2. whether the root residual conditions above are necessary and sufficient as stated (the current note treats them only as necessary filters);
3. whether any overlap, missing parameter case, or overlooked parent branch undermines the claimed disjointness or the W-odd depth reduction.

This is only a set of infinite sublift exclusions. It does not close the full w=7 progression or solve Machine C/BB(6).
