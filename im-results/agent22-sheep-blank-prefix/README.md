# Actual blank-start Sheep orbit covers every even residue mod 32,768

**Agent22, 2026-11-04. Intermediate exact finite arithmetic evidence, not an infinite-orbit theorem.** This result concerns the **single authentic blank-root Sheep even-section trajectory from 10**, rather than synthetic residue graph edges that can choose different integer representatives. Its computational scope is finite and does not establish the holdout's nonhalting behavior or BB(6).

## Exact finite result

Let E be the source-certified Sheep first-even nonterminal return described in [Agent16's original-source bridge](../agent16-sheep-even-return/README.md). Set x_0=10 and x_(n+1)=E(x_n) for the finite segment on which this is defined.

A new independent direct arithmetic implementation in [blank_quotient.py](blank_quotient.py) verifies that **all 157,869 states x_0 through x_157868 exist, strictly increase, remain even and are nonterminal**. The set of x_n modulo 32,768 over 0<=n<=157,868 is exactly the set of **16,384** even residues 0,2,...,32,766. The last new residue first occurs at section index **157,868**. Its counter has **126,782 binary digits**.

The reproducibility hash is SHA256 of the 16,384 unsigned 32-bit little-endian first-visit indices in ascending residue order:

~~~text
62e4c30f24fcf82bf42734abaaa9bccd73f99b9e5ecfd3724b12af27d9d91e95
~~~

The checker validates the exact hash, coverage cardinality, distinct first visits, seed 10, exceptional odd-part-three branch, legal nonterminal transitions, and the first complete-coverage index. It requires Python 3.10+ standard library only; execute **python blank_quotient.py**.

## Exact finite-trace consequence

For every 1<=p<=15, reducing the entire even residue set modulo 2^15 onto modulus 2^p is surjective on even classes. Consequently, for any predicate P(x) determined solely by x modulo 2^p, if P(x_n) holds for every true blank section state on this finite trajectory, then **P contains all even residue classes modulo 2^p**. The same conclusion applies to any predicate claimed to hold for the entire genuine blank-root E orbit.

This is an exact seed-dependent finite obstruction against low-precision congruence-only exclusions. It differs from the all-even-modulus **synthetic** quotient connectivity of [Agent22's earlier work](../agent22-sheep-mixed-hub/README.md), whose edges may originate at chosen positive integers, and complements the stronger global inductive-Presburger no-go argument of [Agent40](../agent40-sheep-coherent-audit/NO-PRESBURGER-INVARIANT.md). The finite observation motivates considering correlations involving unbounded precision, history, or exact integer values.

**Evidence boundary:** The original-source connection of the E section to the machine is an existing checked theorem; the new 157,869-state arithmetic computation is independently reproducible Python evidence, without a separate Lean-kernel replay of all those steps. No infinite reachability, nonhalting, universal BB(6) bound, or external academic novelty is inferred.
