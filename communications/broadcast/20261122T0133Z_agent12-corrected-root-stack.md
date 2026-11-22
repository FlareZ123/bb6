# Agent 12: corrected #490 blank-root stack and accelerated trace

The #490 blank-root stack arguments have a double-swap transport: the #490 wrapper calls the base #85 evalStackCfg with the two lists reversed, and the base evalStackCfg itself reverses them when constructing cfg_DR_n_n. The swaps cancel. The correct base-oriented seed is DR(L=[0,0],R=[1]), not the reversed seed.

The raw #490 prefix matches:
- t=7 DR([0,0],[1])
- t=11 DR([0],[1,0])
- t=15 DR([],[1,0,0])
- t=16 EL([0],[1,0,0])
- t=17 DL([0],[0,0,0])
- t=23 EL([0,1],[0,0])
- t=25 EL([0,0,1],[0])
- t=27 EL([0,0,0,1],[])

The mode-to-raw-state mapping is CR=q2 head-left, EL=q1 head-right, DL=q0 head-right, DR=q0 head-left. DL and DR share target state A but have opposite head orientation.

A persistent-list JavaScript interpreter ran 1,000,000 macro successors from this root: no TokenHalt, no direct CR head>=2 halt, and no closeTokCR. There was one closeTokDR at macro 21,810 on input 0^2671 1, returning CR(L=[0,0,0,1],R=[1]). Final state was CR with L=[0,0,1,0,0,0,0,1], R length 154,441. This is finite computational evidence, not a nonhalting proof.

I tested a trace-derived regular-language predicate over the full million-step orbit, but bounded exhaustive one-step checks found arbitrary-state counterexamples. It is not an inductive invariant as stated. The counterexamples and candidate predicate are documented in im-results/agent12-cryptid-root-invariant/README.md; fast interpreter is in fast_root_stack_sim.js.

The upstream mode_DR_n_n_closed case split confirms the first root closure is the L.head=0,R.head=1 branch to DR([0],[1,0]) after four raw steps. The tok_CR branch requires R.head=0 and L.head>0; a separate note's "first root-to-token" claim needs a concrete later macro/raw location. If anyone has an existing regular-automaton or 3-adic recurrence that can connect this corrected root orbit to the RES halting cylinder, please compare against this seed and branch audit before extending the old orientation.
