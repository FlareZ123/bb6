# Weighted first-write normalization for the complete BB(6) search

## Statement and current evidence

For a total six-state two-symbol table M, define a partial state map Z_M(s) to be the successor of the transition on (s,0) if it writes zero, and undefined otherwise. For an endpoint t with undefined Z_M(t), define D_M(t) as the finite set of d in {0,...,5} for which there exists s with Z_M^d(s)=t. Every terminal path is simple, so this computes the exact set of possible blank delays. Directions affect only the displacement of an all-zero tape.

For every B>=6, the universal canonical-table halting-score bound B is equivalent to:
for every machine M with A/0=1RB and every ordinary-move halting time k of M, every d in D_M(A) satisfies d+k+1<=B.

Both directions are proved: a halter with no write-one move has score <=6; any other halter factors as a simple zero-writing prefix and the first-write-rooted suffix. State permutation, reflection and translation normalize the suffix to 1RB while preserving the prefix graph and the suffix time. Conversely every delay on a 1RB halter is realized by re-rooting its unchanged table at a state attaining that delay. The +1 is the final halting query. In particular an ordinary 1RB-only upper bound B does not suffice without the weight; a B-5 bound suffices, and exact offsets can be smaller.

* [BlankDelayKernel.lean](BlankDelayKernel.lean): generic terminal-path uniqueness, distinctness, five-move bound and exact finite delay-list characterization.
* [BlankDelaySource.lean](BlankDelaySource.lean): exact canonical-table runtime correspondence, normal form and realization, using the existing RootShift, FirstStep and WriteOneDrift interfaces. The generic kernel and this entire proof body passed local Lean 4.36.0-rc2 (commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a) with a reconstructed local model of the relevant repository definitions and theorem bodies. All five exported profiles were [propext, Classical.choice, Quot.sound]. This is a local preflight, not yet original-source acceptance.
* [WeightedFirstOneCover.lean](WeightedFirstOneCover.lean): proposed integration with the original CrossUpper and TwoCylinder source: a Cover of firstOneCylinder with the weighted predicate and a raw halting witness are sufficient for ExactBB6. The adapter still needs its original-source compile and audit.

## Why this matters for the upstream TNF interface

The previous ZeroPrefix theorem removes precisely one 0RB move. This extension proves all possible zero prefixes terminate within five moves or cannot be part of a halting computation, and preserves their full scores without retaining a separate global 0RB queue. It answers the offset issue in the Critic's 24 November TNF-to-two-cylinder communication, conditional on a complete weighted 1RB enumeration.

A sparse 1RB halting leaf must account for zero-symbol instructions which its canonical run never queries. The correct maximum is over all compatible total completions and their D_M(A), not a single arbitrary completion's graph. An existing sound nonhalting leaf is automatically weighted-safe; a bound at least five below the target is also automatically weighted-safe. For near-bound halters, compute the possible incoming simple zero paths over the partial table, or complete its at most five remaining zero slots. This does not prove the upstream TNF enumeration's completeness, nor supply the champion's exact score, nor establish a new numerical BB(6) bound.

## Next gate

Compile the source closure using the existing manual agent13-coverage workflow target weighted-first-one, then verify exact sparse possible-delay lifting and adapt the actual upstream TNF queue/deciders to weighted Cover leaves. No duplicate global enumeration is required for the 0RB prefix issue once the source theorem is accepted.
