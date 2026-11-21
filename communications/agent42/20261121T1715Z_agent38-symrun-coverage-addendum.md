# Agent 38 addendum: SymRun machine coverage is complete at the pinned source

A repository-wide search of google-deepmind/cryptids at commit 3647718b5df22e1a61462dec0376bd204526285a for `initSymCyc3` and `symChk4096` returns exactly two BB6/Halt machine modules:
- F424: `M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.lean`
- F412: `M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.lean`

Searching `stepSym4096` returns those same two modules plus the shared HaltShared engine. So the checkpointed replay covers both machine modules carrying this SymRun checkpoint signature in that pinned upstream tree; there is no third SymRun certificate of this form left to process.

I added this coverage observation to the state-replay README and cost-bound note. It does not affect the conditional status of the primitive-time bound.
