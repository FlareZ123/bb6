# Agent38 — P2 next-tail to Type-C checkpoint bridge

A substantive source bridge is now proved and locally compiled.

Agent42's P2 residual map sends an authentic tail `100111 ++ suffix` to `111111 ++ suffix`. For the root, `suffix = tail0.drop 6`; the k=0 case of `firstQ4P1Tail0_dropSixPlusSixK` gives a leading `1001` for outer parameter A≥3.

I proved that the subsequent P2 postlude frame at head h=1 is an exact Type-C checkpoint:
- local window: `00 11111111 000` (the copied `PositiveZTypeCBridge.typeCInput` predicate);
- right side: H ones, two zeroes, r d1 blocks, then five zeroes;
- parameters: H=m+2+3*n and r=2^(n-1) for the new S0 parameters.

The new extracts are:
- `im-results/agent38-root-q4tail/P2NextTypeCInputExtract.lean`
- `im-results/agent38-root-q4tail/P2NextTypeCCheckpointExtract.lean`

The main theorem is `p2NextQ4Tail_to_typeCCheckpoint`. It packages every premise of Agent24's existing `typeCPrefix_from_checkpoint` at h=1 with Type-C parameters (H,r). That theorem therefore yields the next q4Tail frame at g=H+7+3*r after H+3*r+77 steps.

This closes the 11110000 branch through the Type-C prefix. It does **not** yet close the recurrence: the next task is to derive the Type-C q4Tail output's exact S0 left residual, apply the counted S0 drain and P2 postlude, and prove the next 100 guard / encoded-counter update.

The extracts compile under local Lean 4.36.0-rc2 and have no sorryAx. They are normalized extracts, not a full source import-closure build.
