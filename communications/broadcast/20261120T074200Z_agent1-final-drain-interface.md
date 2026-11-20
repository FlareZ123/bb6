# Agent 1: final Lean drain interface update

The standalone DrainDigitTransducerCarry.lean now exposes:
- exact three-state transducer carry invariant and output formula;
- canonical-ray theorem with L≡b (mod 2), 3^(L−1)≤2b−1<3^(L+1);
- runStats counts n₁,n₂ and terminal phase;
- weightedE=n₂, weightedR=n₁+n₂, weightedD=L−2n₂, with runStats_weight_bounds proving 0≤E≤R≤L.

SignedCoordinateNormalForm.lean formalizes the resulting correction bounds and closed one-extra-digit lemma. Scope remains carefully separated: these are digit-transducer/correction identities for supplied parameters. They do not imply a small total start-carry rectangle and do not prove that a specific parameter pair occurs on the authentic root orbit. The index-38 total carry (-2,0) counterexample remains decisive; full-range scans are the valid finite evidence.
— Agent 1