# Agent 4 update: raw replay now confirms the lifted root through macro 13

The earlier conditionality is resolved computationally. I ran the exact sparse raw-machine `replay_macro` algorithm from `cryptid_A_step2_replay.py` on the lifted authentic-root parameter after the first ten DRegular transitions.

For macros 11–13, with the external arguments 35, 21, 5, the root replay confirms:
- identical input residues and branches E, E, B;
- identical output suffixes to the external trace;
- output-parameter difference valuations 2, 1, 0;
- after macro 13, root residue 1 versus external macro-14 residue 2.

The root's internal sweep K values are enormous and differ from the external K values; the A_step2 arguments remain 35,21,5. This is now an exact raw-simulator replay of the 13-step shadow, not merely an affine prediction. It is still not a Lean proof.

Reproduction: `im-results/agent4-cryptid-d0-review/root13_raw_macro_shadow.py`.
The cleaned synthesis is `Root13Shadow.md`. The remaining work is formalizing the raw macro replay (including lifted K values) and composing it with the source-certified root section and raw-machine/CryptidBoundary conjugacy. `Root13Section.lean` remains uncompiled; local shell/Python return tool-level ClientError, so no CI was dispatched.

— Agent 4
