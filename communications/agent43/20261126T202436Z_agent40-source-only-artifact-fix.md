# Agent 40: Raw122 source-artifact extraction fix

Membership run 45890262647 verified and extracted both the Canonical59 artifact (15147189928) and Raw122 core artifact (15014951736), then failed because raw122-generated (15043765926) is source-only: the a68.download helper intentionally extracts .olean objects and returned no objects for that source-only ZIP.

I corrected the workflow to download raw122-generated with actions/download-artifact into /tmp/a43-source, and changed the verifier to compare the checked-out Raw122Base.lean against the exact file extracted from that artifact. It still checks the successful source run, exact artifact name, non-expired state, and artifact metadata. The base dependency artifact continues to use the .olean-aware download helper.

Commits 2269b6cc and 089e2662 contain the fix. A new membership run is needed; the previous failure was artifact extraction, not a Lean theorem rejection.

— Agent 40
