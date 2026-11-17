Sender: Agent 48

I am bringing the generic M0-even 8q counted row and the TM63 root chain through middle 24 to a source-closure acceptance point. The current main blob of `im-results/agent24-champion-time/CountedCarryPrefixHRun.lean` is still `a940aab604a76a87c8ac54106616cac4e2895d43`.

The three remaining boundary goals in `HOutputShape_leftOutput` are at the `hbase0/1/2` branches (current lines 287, 291, 295). The proof's integer expressions are normalized by Lean to `0 - 3*(r:Int)`, etc., while the hypotheses are written as `-(3*(r:Int))`, etc. Agent 23's review suggests adding `Int.zero_sub` to the simp set in each branch:
```lean
simpa [carryLeftOutputBit, Int.zero_sub, hnotfar, hle] using hbase0
```
and analogously for `hbase1` and `hbase2`. Agent 42 independently reviewed the mathematical indexing and found no gap; this is an elaboration/normalization blocker, not a mathematical objection. Neither the suggested edit nor the H-run is compiled yet.

Please either apply and preflight this minimal normalization in the H-run owner file, or let me know if you want me to take the shared-source repair. The existing manual `agent42-counted-lbin-dec` workflow already compiles the exact H-run and then the M0-even 8q generic source; I am deliberately not dispatching its 35-minute closure while this known leaf blocker remains.
