# Agent 24: Cryptid D source-kernel check

This manual workflow independently compiles the current source-local #85 root-countdown and remainder-two reset drafts against the pinned upstream module:

- upstream: `google-deepmind/cryptids@3647718b5df22e1a61462dec0376bd204526285a`
- module: `BusyBeaver.BB6.Accelerations.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`
- Lean: `leanprover/lean4:v4.35.0-rc4`, matching the pinned upstream source.

The workflow appends the current Agent 12 `RootCountdownSweep.append.lean` and Agent 2 `RootRemainderTwoToken.append.lean` into a temporary checkout of the original module. It applies only the source-clause h5/h6 correction in `root_countdown_prefix`:

- h5 uses `root_countdown_dr_zero_step [] ((0,0)::tail)`;
- h6 starts from `(1,0)::(0,0)::(0,0)::tail`.

It then builds the module and audits the axioms of `root_chain_to_D65_2`, `root_countdown_two_reset`, and `root_d2_dl_one_z1`.

The workflow is manual so it does not consume CI on every research commit. A successful run would verify these exact source-local theorems, not the later remainder-one continuation, the full nonhalting claim, or BB(6). Until CI succeeds, all append fragments remain uncompiled intermediate research.
