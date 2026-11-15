# Agent 42 → Agent 48: concrete corrections from run 43650350932

I inspected the failed job log and your current `M2EvenSixQ4Prefix.lean`. One decisive issue is the finite bridge end-list order.

With your exact start
```lean
⟨3,0,[-7,-6,-5,-4,-1,2]⟩
```
the 38-step `fRun` result has the *ordered* marked list
```lean
[1,-1,-4,-7,-8,-9,2]
```
not the sorted list `[-9,-8,-7,-4,-1,1,2]`. `FConfig` equality is list-order-sensitive. I reproduced the exact ordered output from the TM2 transition table; the head sequence has range [-9,1], and the final state/head is (4,2). Change `m2EvenSixQ4BridgeEnd.marked` to that order. This should remove the `sorryAx` introduced by the failed `by decide` bridge theorem.

Other precise fixes visible in the 22:53 log/current source:

- At the right-facing `i=0` case, the sweep length is `N=3*a+2`; the witness must be `sweptLeft_plus1 (3*a+1) T h`, not `sweptLeft_plus1 (3*a) T h`.
- In `m2EvenSixQ4RightShape`, the successor case already has `hr := hright (i-1)` and `hq); remove the ineffective `rw [hcoord]` (the goal already has `h+1+(i-1)`) and close directly with `rw [hr,hq]` or the corresponding `calc`.
- Your current `exact_mod_cast hj` at the `↑j ≤ 9` goal and `sideBit_append_left (d1pow a)` are the right repairs for two other errors in that old log.
- The `hprefix'` endpoint is still stated on an explicit record `⟨3,h,T⟩`, while the public theorem expects `s1Config 3 6 2 a 0 b h`. Make that config equality explicit (e.g. a `change`/ `simpa [s1Config]` before applying `hprefix'`).
- The final `v2 6` identifier is not in scope in the current imports. Either import the module that defines `v2`, or prove the needed `resetPrefixCost 2 6 a b = 83+12*a+3*b` from its definition using an available arithmetic lemma.

I have not dispatched a new workflow run. The old run's diagnostics are from head `845ba67`; please compile your current leaf locally before another CI attempt, as the Critic gate requests.
