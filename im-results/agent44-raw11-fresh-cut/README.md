# Raw11: complete first-fresh-state cut

Parent: `1RB---_1RC---_0LA---_------_------_------`, raw residual 11 / canonical index 7. This is a **local weighted-TNF refinement**, not a proof of the parent or BB(6).

`Raw11FreshCut.partition` proves that every quotient-compatible completion satisfies `WeightedBound 18` or is quotient-compatible with one of the exactly 116 retained cylinders in `Raw11FreshCut.frontier` (namespace `BB6.Agent44Raw11`). `cover_from_frontier` consumes bounds on all 116 at any common B >=18. The exact tree stops at the first introduction of D, so q0/q32 certificates can be routed into the true parent rather than mistaken for its exhaustive roster.

Discovery: 29 first-hole splits, 292 translated cycles, 27 total closed three-state subsystems, and one expanding-sweep nonhalter with just five defined rows. Maximum first-hole index 12, hence weighted bound 18 including the halt query and at most five incoming blank steps. The sweep `1RB1LA_1RC1RB_0LA---_------_------_------` returns from C on the left blank of a block of 2n+2 ones to the corresponding configuration with two extra ones, in 4n+7 ordinary moves. It never queries the seven unspecified entries. Generic closed-subsystem lemma treats all remaining open three-state total tables.

Local Lean 4.36.0-rc2 compilation succeeded using original accepted canonical77 artifact 14997966221 and exact repository CanonicalPartial.lean (blob 0542d92dfb937b630dfd24d11983aa3c826e911a). Printed axioms: partition and consumer [propext, Classical.choice, Quot.sound], count [propext, Quot.sound]; sweep and subsystem [propext, Quot.sound]. No sorryAx or native_decide. This is artifact-backed local checking, not a new repository CI run. Generate with `node generate-fresh.cjs`; generated Lean blob ac7fdd101608cf3d6bf8b23f3a124884ee3347b5 was checked locally. The emitter is not a proof oracle; Lean checks exact first-hole queries, certificates, and all normalized child cases.

Next: route the existing q0/q32 bank into these cylinders, close additional first-D-entry branches, and retain their exact complements. Do not claim a reduction of the global 64-parent roster until the parent is fully covered.
