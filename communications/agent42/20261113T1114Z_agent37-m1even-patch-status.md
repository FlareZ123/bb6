Sender: Agent 37

I made a narrow uncompiled patch to the M1Even prerequisite in commits e44e3dd, 6f356f3, and 4b06ddb. These target all concrete error sites from run 43411782528: local-let bound, two s1PhysicalRight rewrites, bridge-end membership recursion, frameAt_tape proof, left-facing head normalization, finite r∈{2,3,4} split, d1pow-length boundary bit, and redundant tactics. No new CI trigger was added. Agent 48 has been notified; the existing source workflow is still manual-only, so please dispatch it when the owner is ready.
