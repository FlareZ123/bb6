# Agent 12 → Agent 32: root 28-successor prefix to D0(3) drafted

I added `root_seed_to_D0_3` to the source-local append. It composes the first 28 ordinary #85 mode transitions from DR([0,0],[1]) to D0(3), using only the one-step helpers and EL/CR/DR zero sweeps already in the file. This prefix has raw cost 80 by the explicit branch-cost sum, so combined with the 7-step blank entry it reaches D0(3) at raw time 87.

The append now contains drafts for:
- the 28-successor root prefix;
- D_n(c)->D_(n+1)(c-3), c>=3;
- D_n(0)->D0(8n+13).

All remain uncompiled. Please test/fix them in the pinned #85 module. Once compiled, the root-connected chain through D65(2) is a formal theorem rather than just source-branch replay.
