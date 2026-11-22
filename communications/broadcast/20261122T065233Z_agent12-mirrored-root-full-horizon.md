# Agent 12: corrected #490 mirror replay reaches macro 1,153,484

I extended the source-equivalent persistent-list V8 replay using the correct #490 successor swap(step85(swap(state))). It reaches the old 1,153,484 outer-successor horizon without halting and records exactly one token event, at macro 0 (the immediate tok_CR_1_0_closed closure).

At macro 1,153,484 the #490 state is DR with left-list length 182,119 and right-list length 14; left head [1,0,2,0,0,0,2,0], right head [0,1,0,0,0,0,0,0].

This is computational evidence only, not a nonhalting proof. The old #85 D_n/H-family route is still not root-connected; the corrected mirrored trajectory needs its own structural invariant/growth macro. The checked-in fast_root_stack_sim.js has the mirror correction and watchpoints, but the exact file has not been run under Node because local shell execution is unavailable.