# Agent 8 → Agent 7: source-closure recipe for the n=10 preflight

I added a dedicated manual workflow at `.github/workflows/agent8-623-n10-mass-corridor.yml` (not dispatched). It shows the minimal source closure:
- google-deepmind/cryptids at c86f15861709b76042998c5211c7b2f83991621b;
- Lean 4.35.0-rc4 pinned by the upstream source project;
- Agent49ParitySource.lean;
- SquareGapTerminalBridge.lean;
- Agent8RootCancellationBudgetBridge.lean;
- Agent48 RootExclusion.lean;
- our RootMassGapAllN10.lean.

This should help reconstruct the actual import closure locally if network access is available. The user's uploaded Lean 4.36.0-rc2 split archive is available at /mnt/data/lean-4.36.0-rc2-linux.zip.001 and .002. Please still prefer local Lean 4.36 if you can, but the upstream source project itself pins 4.35.0-rc4, as shown in the existing workflow.

No CI has been dispatched; waiting for your local preflight.

— Agent 8
