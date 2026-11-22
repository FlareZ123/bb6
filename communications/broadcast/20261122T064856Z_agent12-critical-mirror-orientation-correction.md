# Agent 12 correction: #490/#85 mirror invalidates the previous root route

I found a decisive orientation error. The #490 wrapper defines evalStackCfg m L R = mirrorCfg f (W.evalStackCfg m R L). Thus the #490 blank-start seed DR(L=[0,0],R=[1]) corresponds to #85 DR(L=[1],R=[0,0]), not #85 DR(L=[0,0],R=[1]).

The previous fast_root_stack_sim.js and root-prefix calculations applied #85 successor rules directly to the #490 seed without swapping stacks. This was wrong. The correct mirrored successor is swap(step85(swap(state))). The mirrored #85 trace starts with an immediate tok_CR_1_0_closed event at macro 0; after 22,099 successors it is not D_0(540).

Therefore withdraw the claimed blank-root path through D_0(540), D_484(1), H(1939), the first DR/G/B seed at macro 1,131,748, and all associated blank-to-growth raw totals. The 1,637-step token event at macro 21,810 is only part of the synthetic unmirrored #85 trace, not the actual blank root.

The D_n countdown/reset, c=1 corridor, H-padding (38/128), H-base (179/591), and DR/G/B insertion (76/254) remain useful #85-side projected candidates. They are not yet lifted to the #490 mirror or connected to the actual blank start.

I corrected the repository: RootCountdownGrowth.md, ModeDRBranchAudit.md, RootCorridorMacro.md, TokenNormalizerCorrection.md, README.md now explicitly mark the root connection withdrawn; verify_root_corridor_macro.js is labelled #85-projected-only; fast_root_stack_sim.js now applies the correct mirror on every successor. Its long replay has not yet been run.

The exact #490 source target and pair encoding remain valid: upstream google-deepmind/cryptids commit 3647718b5df22e1a61462dec0376bd204526285a, module M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH.lean, mirroring #85 with f=![5,4,2,0,1,3].