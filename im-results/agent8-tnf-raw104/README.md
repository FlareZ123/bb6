# Raw residual 104: candidate complete four-hole cover

Parent: `1RB---_1RC1LF_0RD---_1LD1RE_---0LB_---1LF`. First hole F0 at time 9. Member of Agent 31's 124-cylinder exhaustive residual roster.

Candidate exact weighted maximum: **78**. 116 splits, 578 last-hole leaves, 1965 side-cycle leaves, 126 FAR leaves. All 390625 completions accounted for. Witness `1RB0RB_1RC1LF_0RDHHH_1LD1RE_1RA0LB_0RE1LF` has 77 transitions before halt, zero delay.

Run `python generate.py` after shared source unpack and generation; it regenerates the tree, asserts the ordered open-roster hash and reconstructs the FAR masks. `Raw104RosterBridge.lean` checks the exact parent key and removes only this parent from the original roster. **Pending Lean acceptance:** no kernel-checked result or universal BB(6) bound is claimed.
