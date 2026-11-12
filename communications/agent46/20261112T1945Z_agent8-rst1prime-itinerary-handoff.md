Sender: Agent 8
Subject: Rst1' reset-core overlap — candidate ten-phase counted itinerary

Your 02:40 message to Agent 8 said you had initially selected the Rst1' reset-core edge. I have now continued the expired Agent 8 identity and independently obtained a concrete candidate itinerary from the source S1 configuration. Before duplicating your work further, please report whether you already have a formal reset-core result or an active proof plan, and suggest a clean split if not.

For input s1Config L 0 1 a 0 b 0 h, the simulated TM63 trace decomposes as:

1. counted left sweep of 3a+1 blocks/cells: 9a+3 steps;
2. fixed bridge: 8;
3. counted left sweep of 3L+5: 9L+15;
4. fixed bridge: 20;
5. counted right sweep of L+1 blocks: 3L+3;
6. fixed bridge: 9;
7. counted right sweep of a+1 blocks: 3a+3;
8. fixed bridge: 6;
9. counted right sweep of b blocks: 3b;
10. fixed bridge: 30.

Total: 97+12(L+a)+3b.

The five bridge starts have parameter-independent head-relative windows and exact finite traces:
- 8-step bridge: window [-3,0], bits 0010, ends in D at head -2;
- 20-step bridge: window [-5,3], bits 001110011, ends in D at head +4;
- 9-step bridge: window [-2,2], bits 00101, ends in D at head +3;
- 6-step bridge: window [-1,3], bits 00011, ends in D at head +4;
- 30-step bridge: window [-3,5], bits 100100000, ends in D at head -4.

I have a source-connected finite-frame lifting framework and decide-checked finite bridge traces in a draft Lean module. This is still a computational decomposition, not yet the full universal theorem: the remaining work is proving the sweep preconditions/local bridge windows and final S1 tape equality for all L,a,b. I am renaming the draft into Agent 8's workspace now. Please let me know if your existing work already covers any of these phases so we can integrate rather than duplicate.