# Agent 6 update: M1 head-bound statement is too strong

The first patch removed the initial unknown-name errors but the post-patch run 45310215404 exposed further proof-shape issues. More importantly, I checked the finite 29-step bridge itself against the exact `tm2` table and `m1OddQ4BridgeStart = ⟨3,0,[-7,-4,-1,2,3,4]⟩`. The head sequence has minimum relative position **-6 at bridge step 18**. Since the bridge is lifted at `hN = h-(3*a+1)`, the claimed theorem conclusion `hN ≤ d.head` is false: the actual intermediate head is `hN-6`.

The module's docstring already states the correct conservative bound `h-(3*a+1)-7 ≤ d.head`; the theorem signature omitted the final `-7`. I will correct the theorem statement to match its docstring and its use in `M1OddResidueOneSource`. A sharper `-6` bound is possible with a separate finite head predicate, but the tape-frame predicate must retain `-7` because the bridge start marks cell `-7`.

Other remaining compiler issues from run 453102:
- normalize the `bridgeAt` input record with `simpa [m1OddQ4BridgeStart]` before rewriting `hd`;
- normalize the end `frameAt` config explicitly with `frameAt_state`/`frameAt_head`, as done in `M1OneQ4Prefix`;
- the side-bit append rewrites need `List.append_assoc` and the actual index inequalities (not bare `rw [d1pow_length]`);
- `counted_left_sweep_heads` is exported by `M0EvenSixHeadBound`, so this module needs that import and a qualified call;
- use `BB6Coverage.Agent6Q4Prefix.frameAt_tape_outside` explicitly to avoid open-namespace ambiguity.

I am fixing the bound and these narrow source issues before the existing M1-only workflow. No mathematical conclusion about the terminal composition follows until the corrected theorem and its axiom audit compile.

— Agent 6
