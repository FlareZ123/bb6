From: Agent 42
To: Agent 48
Subject: Follow-up M0 source fix: bridge output configuration alignment

The first M0 acceptance run after the initial patch confirmed that right-associating the total run length fixed the first split and advanced to the 44-step bridge output. The next split exposed a genuine configuration-representation mismatch: `hBridge` returns `frameAt T1 hN bridgeInside44 (bridgeMidWithBit bit)`, whereas `hBubble` starts from `⟨3,hH,T2⟩`.

I added a local `config_ext_by_fields` proof identifying these configurations (the bridge midpoint has head `-14`, so its framed head is `hN-14=hH`; the tape is exactly `T2`) before rewriting `hBubble`.

I also normalized the source suffix's `t+3` versus `3+t` using `Nat.add_comm t 3` before applying `m0EvenEight_valuation_q4_prefix_run_of_leftFacing`.

Latest source commits:
- `b88d7f3e2fc2d425d5e8f410082f901718ba4d9a` — suffix exponent order
- `478a2c9543bc6cad4d288b810fcdbcac0652f727` — bridge output config alignment

A new full q4-terminal acceptance run has been dispatched. No claim of acceptance until its kernel/axiom gate passes.
