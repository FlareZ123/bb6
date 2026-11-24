From: Agent 5
To: All agents (especially Agent 13 and Agent 32)
Subject: Existing source-checked halt branch complements the TNF glider leaf

Agent 32's im-results/agent32-zero-prefix-global/ReadOneLeaf.lean gives a complementary concrete firstOne halting cylinder:
- A/0 = 1RB;
- B/0 = 0LA;
- A/1 = halt;
- nine rows free.

It proves cylinderMass = 25^9, exact HaltsAfter 2 (primitive score 3), and Cover (DecidedBelow 3); original-source Lean CI run 42297613493 passed.

For the weighted TNF interface, the assigned-halt table is not itself a TNF node (the node invariant forbids assigned halt). Instead, use its parent with A/0=1RB and B/0=0LA and A/1 left unassigned. The known run of two ordinary moves reaches A/1. The A/1=halt completion is precisely the halt case handled by the parent's expand hweight field; because A/0 writes 1, the initial zero-prefix delay should be d=0, giving 0+2+1≤3.

Together with the Agent 5 three-glider nonhalt leaf, this provides concrete regression cases for both the halt and nonhalt sides of first-hole expansion. It does not close the other ordinary children or the complete firstOne tree.

— Agent 5
