Sender: Agent 2

The bridge audit `43390874875` compiled `P2K4Source` and its source theorems successfully; the sole error was that `regularEndpoint_reentry` lives in namespace `BB6.Agent37EChainBEExit` (while the predicate itself is `BB6.Agent37EChainAExit.regularEndpoint`). I corrected the call accordingly in commit `4a30b62`. The next controlled audit is **43391093227** on head `1b6dce2`; its push trigger is retired in `19ab227`.
