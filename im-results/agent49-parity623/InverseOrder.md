# Ordered inverse branches of machine #623

Agent 49, 25 November 2026. Intermediate result, not a machine decision.

Let E and J be the positive-budget excess and signed first-counter drift of [DrainCorrectionGrowth.lean](DrainCorrectionGrowth.lean). Let F(b)=3b+E(b), H(b)=F(b)+J(b), G(b)=b-J(b). The exact recurrence yields:

* H(b+2)-H(b) is always one of 4, 8, 10, even across arbitrarily long ternary carries.
* J(b+2)-J(b) is at most 2, hence G is nondecreasing on each parity class.
* The H-gap is 4 for b=1 mod 3 and 8 for b=2 mod 3. For b=3q>0 it is the H-gap at q-1. At b=0 it is 10.

These statements follow by strong induction; no numeric cutoff is needed.

## Quantitative inverse contraction

The original source-linked inverse in [LogarithmicInverse.md](LogarithmicInverse.md) and [InverseWindowSource.lean](InverseWindowSource.lean) has a common form on every positive-budget non-axis branch. The target is (x,F(b)+z). After a possible coordinate exchange, the parent is (x+G(b)+c1,b+c2), with branch constants. For ordered targets in the same branch with x'≥x and b'=b+2k, both parent coordinates are nondecreasing. Moreover

    mass(parent')-mass(parent) + 4 floor(k/3)
      ≤ mass(target')-mass(target).

Indeed the difference between target width and parent width is H(b')-H(b)-4k; every three consecutive parity steps include a residue-two gap of 8, while all other gaps are at least 4. This is a genuine unbounded statement about each inverse branch, applicable to ordered parametric terminal families whenever the positive-budget hypotheses and branch feasibility hold. A whole interval can be bounded by its endpoint parents after retaining exact image holes; a fixed branch word composes these order inequalities. This does not prove that every terminal row has an empty inverse tree: branch switching, sparse image membership, and the small-first inverse window must still be handled.

[InverseOrder.lean](InverseOrder.lean) proves the arithmetic theorem for any E,J satisfying the exact recurrence. Lean 4.36.0-rc2 compiled it locally; all axiom reports use only propext, Classical.choice, Quot.sound. [InverseOrderSource.lean](InverseOrderSource.lean) instantiates it on the established E,J definitions. Local preflight used the definition-identical excerpt and existing recurrence lemmas of DrainCorrectionGrowth; the full source-import closure was not rebuilt. No new CI workflow and no claimed change to BB(6) or #623 status.
