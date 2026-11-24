# Weighted first-write normalization for the complete BB(6) search

## Statement and current evidence

For a total six-state two-symbol table M, define a partial state map Z_M(s) to be the successor of the transition on (s,0) if it writes zero, and undefined otherwise. For an endpoint t with undefined Z_M(t), define D_M(t) as the finite set of d in {0,...,5} for which there exists s with Z_M^d(s)=t. Every terminal path is simple, so this computes the exact set of possible blank delays. Directions affect only the displacement of an all-zero tape.

For every B>=6, the universal canonical-table halting-score bound B is equivalent to:
for every machine M with A/0=1RB and every ordinary-move halting time k of M, every d in D_M(A) satisfies d+k+1<=B.

Both directions are proved: a halter with no write-one move has score <=6; any other halter factors as a simple zero-writing prefix and the first-write-rooted suffix. State permutation, reflection and translation normalize the suffix to 1RB while preserving the prefix graph and the suffix time. Conversely every delay on a 1RB halter is realized by re-rooting its unchanged table at a state attaining that delay. The +1 is the final halting query. In particular an ordinary 1RB-only upper bound B does not suffice without the weight; a B-5 bound suffices, and exact offsets can be smaller.

* [BlankDelayKernel.lean](BlankDelayKernel.lean): generic terminal-path uniqueness, distinctness, five-move bound and exact finite delay-list characterization.
* [BlankDelaySource.lean](BlankDelaySource.lean): exact canonical-table runtime correspondence, normal form and realization, using the existing RootShift, FirstStep and WriteOneDrift interfaces. The generic kernel and this entire proof body passed local Lean 4.36.0-rc2 (commit b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a) with a reconstructed local model of the relevant repository definitions and theorem bodies. All five exported profiles were [propext, Classical.choice, Quot.sound]. This is a local preflight, not yet original-source acceptance.
* [SparseBlankDelay.lean](SparseBlankDelay.lean): exact sparse delay enumeration (at most 326 simple paths), a constructive compatible-completion witness for every accepted delay, and the exact uniform-halting-cylinder weight criterion. All these proofs pass local Lean with the same three ordinary axioms; the example A0=1RB, B0=halt, all other rows unknown has precisely delays 0 through 4.
* [WeightedFirstOneCover.lean](WeightedFirstOneCover.lean): proposed integration with the original CrossUpper and TwoCylinder source: a Cover of firstOneCylinder with the weighted predicate and a raw halting witness are sufficient for ExactBB6. The adapter still needs its original-source compile and audit.

## Why this matters for the upstream TNF interface

The previous ZeroPrefix theorem removes precisely one 0RB move. This extension proves all possible zero prefixes terminate within five moves or cannot be part of a halting computation, and preserves their full scores without retaining a separate global 0RB queue. It answers the offset issue in the Critic's 24 November TNF-to-two-cylinder communication, conditional on a complete weighted 1RB enumeration.

A sparse 1RB halting leaf must account for zero-symbol instructions which its canonical run never queries. The correct maximum is over all compatible total completions and their D_M(A), not a single arbitrary completion's graph. An existing sound nonhalting leaf is automatically weighted-safe; a bound at least five below the target is also automatically weighted-safe. For near-bound uniform halters, the exact criterion is now proved in SparseBlankDelay: enumerate simple incoming paths under known and unknown zero rows. Every accepted path can be realized simultaneously by assigning only its own unknown rows, because all its source states are distinct. Thus the maximum over this finite list is attained, without enumerating irrelevant transition completions. This does not prove the upstream TNF enumeration's completeness, nor supply the champion's exact score, nor establish a new numerical BB(6) bound.

## TNF normalized expansion and last-hole rule

[WeightedTNF.lean](WeightedTNF.lean) formalizes the precise branch reduction used by upstream `verify/Enumerate62.v` at pinned revision 33209bc7dc282b38c8cd6be507bfc551fea56108. A sparse node has a cut c with every assigned source and destination label below c. A genuine first hole belongs to a state below c. For an ordinary successor label below c retain it; otherwise swap it with c, fixing every assigned row and the root. Both the canonical runtime and every incoming blank delay survive this permutation. Thus `first_hole_tnf_cover` derives a weighted Cover from the halt weight and only the existing-label plus least-fresh-label branches (four ordinary actions per eligible label). `refine_support` establishes the invariant for the new cut.

The source-independent sparse knownRun semantics proves that a first hole at n ordinary moves yields exactly n+1 for every completion of the explicit halt child. `first_hole_weighted_halt` adds the exact sparse delay. `last_hole_sound` proves the upstream expand' optimization when all other rows are fixed ordinary instructions: every ordinary completion is then total and never halts, and the halt completion is bounded by its weighted score. Dropping the halt leaf without a score proof would not be sound.

All five exported theorem profiles passed local Lean 4.36.0-rc2 with only propext, Classical.choice, Quot.sound, using the reconstructed local interfaces. The proof still requires original-source acceptance and a concrete upstream queue/certificate replay; no finite holdout roster is assumed exhaustive.

## Next gate

Compile the source closure using the existing manual agent13-coverage workflow target weighted-first-one, including the sparse lift and TNF rules, then connect the actual upstream TNF queue/deciders to weighted Cover leaves. No duplicate global enumeration is required for the 0RB prefix issue once the source theorem is accepted.
