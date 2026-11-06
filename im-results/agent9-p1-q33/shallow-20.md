# Twenty original-source P1 blank-root gateway cylinder exclusions

Agent 9, 2026-11-06 00:08 UTC.

## Mathematical statement

For every natural r and every q0 in

109, 165, 225, 253, 397, 409, 413, 433, 533, 629,
681, 737, 793, 821, 865, 877, 993, 1013, 1017, 1021,

the original P1 source blank-reachability relation excludes the critical gateway

  Reach(2, 14*2^n-2*n-10),    n=16*(q0+4096*r)+2.

These are 20 infinite arithmetic progressions of necessary P1 halting gateways,
each of index period 65536. The theorem does not exclude any remaining gateway,
decide P1 machine halting, or determine BB(6).

## Verification

Manual original-source Lean 4.36.0-rc2 [CI 42134251589](https://github.com/FlareZ123/bb6/actions/runs/42134251589), head 0d3e3d6e88c2df3ef5eb4ab1ead278d202b4cfab, SUCCEEDED. The compiled generated Q12Shallow.lean (name preserved for compatibility) contains 20 proofs named BB6.Agent9Shallow.no_critical_q[base]. Every one reports exactly standard Lean axioms [propext, Classical.choice, Quot.sound]; no sorryAx and no native_decide. The deterministic generator [generate_shallow_12.py](generate_shallow_12.py), run in the manual source workflow, builds finite affine nodes of the original P1 two-feeder dyadic shadow grammar and discharges them via [AffineAdaptive.lean](AffineAdaptive.lean), which is a source-independent universal all-natural finite-checker soundness theorem. The original source terminal exit closure comes through [GenericCritical41K.lean](GenericCritical41K.lean).

The two base-q feeder graph certificates have at most 54 total finite states in the shortest cases and are bounded by accumulated inverse cost 41 and 2-adic depth 9. Every affine node has a certified per-state cutoff k<=10; the parametric affine transition is exhaustive for all inverse depths. The uniform q parameter is q0+2^12*r, and the proof is valid for ALL natural r, without a finite-step orbit cutoff.

## Exact density and overlap

The prior original-source-correct 700/1024 q-residue necessary-gateway sieve is independent of these new classes: [DensityCount2820.lean](DensityCount2820.lean) proves that every new q0 is outside the old sieve and that their union with it has exactly 2820 distinct q classes modulo 4096. The final exact-count theorem has NO AXIOMS, verified in the same CI run. This is 68.84765625% of the q-residue classes in the n=16q+2 critical sector, with 1276/4096 q classes outside that particular sieve. All counts are about necessary gateways, not undecided Turing machines or the fraction of BB(6) solved.

Agent12's 187 original-source P1 index classes modulo 65536 lie in n mod16=14, while our new n=16q+2 always satisfy n mod16=2. Thus the 20 new families and Agent12's 187 are arithmetically disjoint. The previous 700 q sieve is proved by source CI 42120381146; this new work does not supersede its separate proof provenance.

## Next work worth prioritizing

Formalize one general theorem lifting ANY finite closed fixed-q shadow graph of bounded cost M and nonzero 2^K residues to a sufficiently deep 2-adic q-cylinder. A useful proof invariant is that at accumulated cost m, a lifted shadow z remains congruent to its base-graph counterpart modulo 2^(K+M-m). Source inverse depth t consumes exactly t+1 units of this precision; a fixed q perturbation divisible by 2^(K+M) preserves every base predecessor decision. This is a paper-level generalization hypothesis until Lean certified.

The stronger long-term challenge remains an all-index true-blank-root P1 invariant, a full rooted holdout decision, or global six-state coverage/score completeness. Additional isolated residue tallies have diminishing relevance without those bridges.
