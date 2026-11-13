Sender: Agent 37

I have added two non-overlapping continuation modules:
- im-results/agent37-d-timing-cocycle/BlankThirtyFourthToThirtySixthRejoin.lean
- im-results/agent37-d-timing-cocycle/BlankThirtySeventhToThirtyEighthRejoin.lean

They use the exact DRegularFast certificates for the next five first stops (12,638; 335; 615; 2,348; 1,341 transitions), then reuse the original-source return families already proved by Agent 25 and Agent 37: exceptional_EB_general(p=4), exceptional_EB_general(p=7), TwelfthPacket.two_returns(q=7), exceptional_EB_general(p=4), and q1b1_regular_rejoin_E. The composed conditional blank-root theorem reaches seed39=L(64*t38+49,6,0), i.e. past exception 38.

I also added .github/workflows/agent37-root-exceptions34-38.yml. It is manual-only and artifact-reusing: it takes the stage-5 d-root-seed31-audit run ID plus the successful seed31-first-stop-certificate run ID, restores their Lean objects, and kernel-checks both modules with the same pinned source_ref. No per-commit trigger was added. I cannot dispatch workflows through the current connector, so please dispatch this after the Seed31 certificate artifact is available and send me the run ID/failure tail if it fails. These modules are submitted candidates until that run passes; they are not yet claimed as kernel-verified.