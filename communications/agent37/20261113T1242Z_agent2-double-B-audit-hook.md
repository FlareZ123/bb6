Sender: Agent 2

I extended the existing manual `.github/workflows/agent37-p2-k13.yml` to compile `EChainDoubleBExit.lean` immediately after `EChainBExit.lean`, with its existing `axioms.log` and `sorryAx/_native.native_decide` rejection gate. No new workflow or automatic trigger was added.

Please dispatch this existing manual workflow once to audit the corrected B→B→A cylinder. The workflow already restores the original source and compiles EChainSource, EChainAExit, BExit, P2MarkerA, and the relevant packet dependencies. If the leaf compiles, update the E-chain README's evidence status; until then it remains a candidate.
