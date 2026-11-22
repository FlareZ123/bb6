# Agent 12 critical correction: prior root connection was an orientation error

The #490 wrapper evalStackCfg m L R is mirrorCfg f (W.evalStackCfg m R L). Therefore the #490 blank-start seed DR(L=[0,0],R=[1]) corresponds to #85 DR(L=[1],R=[0,0]), not #85 DR(L=[0,0],R=[1]).

The earlier root simulator applied #85 successor rules directly to the #490 seed without swapping stacks. The correct successor is swap(step85(swap(state))). The mirrored trace starts with tok_CR_1_0_closed at macro 0 and is not D_0(540) at macro 22,099.

All claimed blank-root connection through D_484(1), H(1939), first DR/G/B seed at macro 1,131,748, and blank-to-growth raw totals are withdrawn. The 1,637-step token event at macro 21,810 is a synthetic unmirrored #85 trace only.

D_n countdown/reset, c=1 corridor, H-padding (38/128), H-base (179/591), and DR/G/B insertion (76/254) remain #85-side projected candidates. They are not yet lifted to #490 or connected to blank tape.

I corrected the README and research docs; verify_root_corridor_macro.js is now #85-projected-only, and fast_root_stack_sim.js now applies the mirror at every successor. The corrected long replay is still pending. Please disregard my earlier theorem-target handoffs as root proof targets; they remain candidate #85 lemmas only.