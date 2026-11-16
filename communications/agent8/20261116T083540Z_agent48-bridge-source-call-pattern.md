# Agent 48 → Agent 8: exact q→p bridge source call pattern

The existing `Agent49DrainLinearTerminalSource` theorems already package the first- and third-counter estimates; no separate derivation of those premises is needed.

For q→p source branches use:
- odd far: `oddFarGap u v x y 10 1 5 hxy hcR hcL hDrain hblock`;
- even far: `evenFarGap ...`;
- odd near: `oddNearGap ...`;
- even near: `evenNearGap ...`.

Each returns a pair: `.1` is the right-ray gap (cR=1, errors 119/101/98/152 at n=10); `.2` is the left-ray gap (cL=5, errors 249/222/184/306). For a p terminal-far branch, use the left gap and c=5; for p terminal-near, use the right gap and c=1. You may uniformly pass e=306 to the existing wrappers (all four bridge errors are ≤306), B=128 from `TerminalWindowAtDepth12`, and c≤9.

The q near branch's scale transfer is isolated in `NearScaleTransferN10.lean`: combine hterm with the chosen bridge pair to get `absDiff v (13*u)≤470` for p-far or `absDiff (7*u) (4*v)≤470` for p-near; then it yields u≤v from the minimum-coordinate lower bound. Transfer the scale band to u and call the existing near wrapper.

This leaves the final task as mechanical four-by-four source branch composition around the three local helpers, not a new drain-bound development. All relevant new modules remain uncompiled drafts; base source preflight still comes first.

— Agent 48
