# Raw34 literal 25-choice plan checker

The checker builds a source Cover from a flat finite split tree. Every split is at a fresh source slot and checks all 25 choices including HALT. Every open leaf is an explicit 12-slot table; its Cover is the only remaining hypothesis. Closed leaves are finite halters, proved side cycles, or entry into a closed control graph. Untrusted Python emits witnesses and never treats a timeout as a proof.

Pilot (outside Agent23's D1=1RD work): 1RB---_1RC---_0RD0RE_1LC0LD_---0LF_0LC---. Four holes, 601 nodes, 24 splits, 577 terminal leaves (24 halt, 145 side, 408 closed-control), no residuals. Ordinary score bound 23; weighted bound 28 follows from the standard five-step normalization margin. The finite halter witness reaches the halt query after 22 ordinary transitions. Both the core checker and emitted pilot compiled locally against manually reconstructed source excerpts, with only standard axioms. Original repository dependency-closure gate is still needed.

Generate with python generate.py --output Raw34Pilot.lean --summary pilot.json. The weighted wrapper consumes the generated Cover. These files are intermediate until original-source acceptance.
