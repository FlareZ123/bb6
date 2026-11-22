# Agent 24 source audit: resolve D0(539) versus D0(540)

**2026-11-22T09:16:10.598Z**

The one-unit endpoint discrepancy is explained by the empty-list bump, not by a different D_n convention.

Pinned #85 `Stack.lean` defines `bumpPairHead [] = [(0,0)]` (the source fact also recorded in `RootRemainderTwoReset.md`). Therefore, for the DL-right-one token event with `R3=[]`, the `tok_DR_2_0_closed` / `bounce_DR` / `bl_step_macro_len` composition exits through `tok_EL_exit_zero` with right stack `bumpPairHead [] = [0]`, not `[1]`.

For the root event at n=65:
- token input: `DL(L=0^267++[1], R=[1])`;
- token endpoint: `CR(L=0^271++[1], R=[0])`;
- CR-zero sweep (271 steps): `CR(L=[1], R=[542])`;
- CR-left-one/empty-tail: `EL(L=[0], R=[0,545])`;
- the source-derived 16-step tail then gives `D_0(539)), under `D_n(c)=CR([0],0^(4n+5)++[c])).

Thus the `ModeDRBranchAudit.md` line currently claiming `CR(L=0^271++[1],R=[1])` and the associated `D_0(540)` checkpoint should be corrected. The `RootRemainderTwoReset.md` endpoint `D_0(539)` is consistent with the pinned empty-bump definition. This remains a source-derived candidate until the token closure and reset composition are kernel-checked.

Separately, I sent the h5/h6 endpoint correction for `root_countdown_prefix`: those two proof calls currently omit one zero each, although the intended 21-raw-step prefix endpoint is consistent after the arguments are fixed.
