# Quadratic-size exact terminal-feeder enumeration

**Agent 48, 7 November 2026.** Original-source Lean verification passed in [CI run 42416997719](https://github.com/FlareZ123/bb6/actions/runs/42416997719), using the pinned Cryptids source and Lean 4.35.0-rc4. This is a sharper exact reduction of the Space Needle halting question. It does not decide the remaining unbounded blank-root reachability problem or BB(6).

## 1. Terminal equation and dichotomy

For a terminal exponent K, an immediate predecessor (q,v) satisfies

E(q,v,K): 2^v(2q+3)+v+3(q+1)=2^K.

The all-natural theorem NeedleTerminalDichotomy.terminal_exception_or_square_bound proves that for every solution with 11 ≤ v, at least one of

    (K+1) % (v+1) = 0
    ((K+1)/(v+1)) % 2 = 0
    2*v = 3^((K+1)/(v+1)) + 3

or

    v*v ≤ 8*(K+1)

holds.

In the first branch, write (K+1)/(v+1)=2r. Then

    v = (9^r+3)/2
    K+1 = r*(9^r+5).

The proof also gives r ≤ Nat.log2 (K+1). Thus all exact cancellation candidates for fixed K can be found by checking only the logarithmic range of r. The implementation checks the exact identity K+1=r*(9^r+5) before evaluating the expensive inverse candidate. This is important: evaluating candidate v K for every logarithmic r without that filter can construct absurdly large 2^v exponents even when the corresponding r cannot satisfy the cancellation equation.

## 2. Exact finite list

[NeedleQuadraticEnumerate.lean](NeedleQuadraticEnumerate.lean) defines

    cancellationValuations(K) =
      filterMap (r in range(log2(K+1)+1))
        if K+1 = r*(9^r+5) then
          if 11 ≤ (9^r+3)/2 then some ((9^r+3)/2) else none
        else none

    quadraticValuations(K) =
      [0,1,...,10]
      ++ {v | 11 ≤ v ≤ floor(sqrt(8*(K+1)))}
      ++ cancellationValuations(K)

For each valuation, the exact quotient candidate is checked by NeedleInverse.candidate. The theorem

    (v,q) ∈ quadraticParents(K) ↔ E(q,v,K)

proves soundness and completeness for every natural q, v, and K. This is not a cutoff justified by experiments.

The explicit list-size theorem is

    (quadraticParents K).length
      ≤ 11 + (Nat.sqrt (8*(K+1))+1) + (Nat.log2 (K+1)+1).

The same bound holds after filtering to quadraticRegularParents(K), defined by the additional sixth-linear condition 6*v ≤ K+4. Consequently the output candidate count is O(sqrt(K)+log(K)), asymptotically smaller than the previous optimized slope-scan cutoff of order K/log(K). The exact source-facing index is K=k+1, so the original-machine condition is 6*v≤k+5.

The original-source bridge [NeedleQuadraticEnumerateSource.lean](NeedleQuadraticEnumerateSource.lean) proves that list membership is equivalent to an actual one-step transition in the pinned original high-level machine. [NeedleRootQuadratic.lean](NeedleRootQuadratic.lean) gives the unfiltered root equivalence. More strongly, [NeedleRootQuadraticRegular.lean](NeedleRootQuadraticRegular.lean) combines the complete quadratic list with the already source-checked sixth-root theorem:

    IsHalt target ↔
      ∃ k q v,
        ReachN (oddTower q v)
        ∧ (v,q) ∈ quadraticRegularParents(k+1).

This is an exact blank-start reduction. It retains an unbounded exponent k and an unbounded reachability predicate.

## 3. Two more cancellation feeders excluded from the genuine root

[NeedleCancellationHoldouts.lean](NeedleCancellationHoldouts.lean) studies the cancellation family at r=3 and r=4. Both are exact synthetic terminal predecessors, and both satisfy the sixth-linear restriction.

| r | K | v | terminal reached by the feeder |
|---:|---:|---:|---|
| 3 | 2201 | 366 | haltTower 2200 |
| 4 | 26263 | 3282 | haltTower 26262 |

The equations and original-source one-step transitions are proved in Lean. Their genuine blank-root status is then decided using the complete generic inverse NeedleGeneralInverse.parents and the exact fixed-target theorem NeedleRootDecisionSource.exact_root_target.

- **r=3:** the feeder has no incoming generic inverse parents, hence cannot be reached from the blank root.
- **r=4:** its exact reverse-parent valuation chain is 4 → 0 → 1 → no parents. The reverse cone terminates before reaching initial counter 1, so the feeder is unreachable.

The parent-list equalities and root-check false results are Lean theorems using native_decide, not unverified output from a simulator. The same file prints the valuation chain for reproducibility.

The r=1 feeder (K,v)=(13,6) and r=2 feeder (171,42) were already excluded by [NeedleRootSharp.lean](../agent20-needle-coprime/NeedleRootSharp.lean) and [SpaceNeedleFifthRoot.lean](SpaceNeedleFifthRoot.lean). Thus the first four cancellation-family members are now excluded from the genuine blank-root orbit. The family for r≥5 remains unresolved, as does the entire square-root-bounded valuation sector.

## 4. Verification and limits

The successful [CI run 42416997719](https://github.com/FlareZ123/bb6/actions/runs/42416997719) compiled the quadratic enumerator, exact source adapter, both root equivalences, and the r=3/r=4 cancellation holdout proofs against the unchanged pinned Cryptids source. It also executed the guarded valuation examples and the reverse-parent diagnostics. No sorry or admit is used in these modules.

The result is a smaller, formally complete list of possible terminal feeders and two further exclusions from the real blank-root orbit. It does not show that every member of the remaining list is unreachable. The Space Needle machine is still undecided, and no exact BB(6) value or universal six-state upper bound follows.
