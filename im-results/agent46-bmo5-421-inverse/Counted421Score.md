# Primitive-transition cost of BMO5 holdout #421

The literal table is 1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE. Counted421.lean uses two natural-number stacks with their least significant bits nearest the head, and defines each table entry directly. The final undefined query counts as one step. Its exact canonical macro costs, section evaluator, and quadratic bound are all proved in Lean 4.36.0-rc2.

Counted421Bridge.lean proves that the counted section endpoint agrees with Cap.f for every positive half-counter. Counted421Score.lean proves a bidirectional exact blank halt score criterion:

    Exact (A,0,0) n none
      iff exists i, rootOf (halt i) = 2
        and n = 8 + arrivalCost (halt i) + score (halt i).

Here arrivalCost is the unique inverse ancestry sum, excluding the final section. The score of any section is at most 100*(2*x+10)^2, so any actual halt at terminal index i has score <= 1000000*8^i. This is conditional, not a decision of #421. The other two BMO5 machines need their own primitive costs.

All three modules locally compiled against exact copied Cap/CapInverse/CapRoot sources, whose Git blobs are e6e69d1190901fccbdf288c8559033e5463190bc, e6b9ea94d3fc6ed918f416938579e49ab6c16d60, and 94880fd4529baa179f6f50a2bf865797cca96b74. Axiom audit of exported theorems: only propext, Classical.choice, Quot.sound. The literal-table encoding is independent of the repository's BB6Coverage representation; a formal transport to that representation is still needed for use as a coverage leaf.

Reproduce with LEAN_PATH=. and Lean 4.36.0-rc2 in this directory:

    lean -o Cap.olean Cap.lean
    lean -o CapInverse.olean CapInverse.lean
    lean -o CapRoot.olean CapRoot.lean
    lean -o Counted421.olean Counted421.lean
    lean -o Counted421Bridge.olean Counted421Bridge.lean
    lean Counted421Score.lean

Next: compress the counted diagonal and C2 drains into closed polynomial costs by band, so exact ancestry evaluation does not iterate exponentially large unary counters.
