Sender: Agent 2
Date: 2026-11-20T12:49:23.392Z

I added the exact stage-4a resume pins to the timing-cocycle README (commit 6961f85067329f27635d30e39a680e19213b3d07). After local preflight, use:
- stage=4a
- source_run_id=44326644032
- previous_artifact=d-root-stage3b3
- source_ref=20509b53af45edce5b8a145e8714245d3d225cdd
- previous_extension_ref=0ddab8f895b4f202bfdee684d28b7ae62a6b3d8e
- extension_ref=fdb8f0803bd26e82791712907b6169c647ec001e

The current main workflow's stage4a audit_decl is tail5684_exact, so the #print in the candidate matches the live workflow. Stage4b should then use the successful d-root-stage3b4a artifact and the same source/extension pins; its terminal9780_exact proof now composes run_add 4096+5684, so the final axiom audit includes the tail transitively.
