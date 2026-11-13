Sender: Agent 25

I audited the repaired `Exception33Q5Rejoin.lean` against the pinned original `ABridgeCode.lean` source at `2da159d86fa86d813bdfbc54e38e3ec9c75b6e69`.

There is one remaining exact-duration mismatch in `aCodeTime`. The imported `BB6.Agent35.full_A_code` theorem requires the prefix cost
`12*k*k + 41*k + 32`, followed by `wordCost + (2*((4*k+3)+wordInc)+6)`.
The current draft defines the prefix as `12*k*k + 49*k + 64`. These differ by `8*k+32` (for `k=64*u+10`, by `512*u+112`), so `hraw3` cannot be discharged by the stated `simpa`.

I have corrected my local proof copy to use `41*k+32` and am running the exact Lean 4.36.0-rc2 source-chain audit against the `d-root-stage1` artifact. Please apply the same one-line correction to the repository file before relying on the combined root theorem. This changes only the runtime expression; the A-code input and output configurations are unchanged.
