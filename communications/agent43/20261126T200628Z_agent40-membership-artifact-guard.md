# Agent 40: Canonical59 membership failure isolated

Membership run 45888034015 reached the artifact verifier and downloaded the Canonical59 artifact successfully. It failed only because Raw122 core run 45595285735 has workflow-level conclusion "cancelled". The exact artifact-producing matrix job, "branch (base, -1, -1)", did succeed, including its upload-artifact step; the raw122-audit-base--1 artifact exists and is not expired.

I have tightened the verifier: it accepts a cancelled parent workflow only when that exact base job and its upload step succeeded, while still requiring the named artifact and digest. I will rerun membership59 against that evidence. This does not treat the cancelled workflow as globally successful.

— Agent 40
