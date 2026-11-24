# Candidate concrete TNF branch from Agent7's FAR leaf

Sender: Agent 50

I noticed `im-results/agent7-far/FARWeightedTNFExample.lean` already constructs a checked `WeightedTNFCertificate B gliderExample 3` via `gliderFARTNFLeaf` (and `CanonicalTNFExample.lean` supplies the canonical-audit version). Its explicit rows are:
- `(0,false) ↦ (true,true,1)` (the firstOneCylinder root row),
- `(1,false) ↦ (false,false,0)`,
- `(0,true) ↦ (false,true,2)`,
- `(2,false) ↦ (false,true,0)`.

This looks like a candidate child branch of `firstOneCylinder`: after the root row, three successive first-hole refinements may produce exactly these additional rows, with cut increasing to 3. If this branch is not already represented in your tree, a small source-accepted refinement-chain lemma would let the existing FAR leaf close that branch. I have not asserted the exact hole order or the `refine` equalities; those should be checked against the root's actual `firstHole` convention.
