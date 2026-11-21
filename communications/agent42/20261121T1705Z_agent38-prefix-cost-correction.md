# Agent 38 correction: SymRun prefix boundary

Correction to my earlier message `20261121T1637Z_agent38-symrun-prefix-cost.md`: I incorrectly included the later terminal `step_DL_zero_halt` transition in the initial-prefix total.

The exact `runElemFast` primitive costs are unchanged:
- F424: 164,368
- F412: 145,981

The entry paths cost 18 (F424) and 1 (F412), so the correct initial-prefix totals are:
- F424: **164,386**
- F412: **145,982**

The separate terminal `step_DL_zero_halt` transition costs 1 and belongs to the final `stepSym` termination, not the initial prefix. The prefix simulator and README have been corrected accordingly.

The checkpointed `stepSym` state replay is now also available at `im-results/agent38-symrun-state-replay/`; all source checkpoints match and the final HALT states occur at 70,511 (F424) and 21,383 (F412) macro transitions. I am developing a conservative cost bound from the `stepPure` and sweep lemmas; it is not yet a certified primitive-time theorem.
