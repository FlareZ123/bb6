# Agent 1: concrete low43 continuation correction

I checked the current `Low43Continuation.lean` candidate against the exact definitions it imports (the `BB429OddExcursion.action/one`, `BB429SourceE1Delta.oneWithDelta`, and `BB429W4HeadMax.runWithMax` definitions, plus `ones`, `tens`, and `junc`).

The theorem `root_low43_C0_to_junc_max` as currently written is **false**:

```lean
runWithMax 119
  (z 2 (true::false::true::true::
    (ones 26 ++ tens 14 ++ ones 6)) false [])
  ≠ some (junc 0 9 25, -45, 1)
```

A Lean 4.36.0-rc2 reproduction of those exact definitions evaluates the 119-step endpoint to state C, head displacement -59, maximum +1. The important parameter detail is that `tens 14` has 28 bits, because `tens (n+1) = true :: false :: tens n`; it is not a 14-bit word.

The exact corrected source-zipper fact is:

```lean
runWithMax 438
  (z 2 (true::false::true::true::
    (ones 26 ++ tens 14 ++ ones 6)) false [])
  = some (junc 23 0 18, -20, 1)
```

I checked this in a local Lean 4.36.0-rc2 harness using the exact imported definitions, with `by decide` (maxRecDepth 32768); `#print axioms` reports no axioms. This matches the independent blank-root trace: the C/0 at raw step 1820 is followed by J(23,18) at step 2258.

There is a further exact continuation:
```lean
runWithMax 909 (junc 23 0 18)
  = some (junc 11 0 62, -37, 28)
```
also checked by `by decide` in the same harness with no axioms. By `runWithMax_add`, the C/0-to-J(11,62) segment is 1347 steps, displacement -57, max +8. Composed with the existing 212-step `low43_C0_record 5 7`, this gives a local J(21,11)-to-J(11,62) branch of 1559 steps, net displacement -41, maximum displacement +24. The endpoint is consistent with the raw root checkpoint at step 3167 (absolute head -29, historical maximum 36).

Thus the 119/45-step route to Junc(12,0,22), and the current `root_low43_branch_to_junc12` theorem built on it, should not be used. The correct next endpoint is Junc(23,0,18), then Junc(11,0,62). I have not yet claimed a physical-root theorem or CI certification for these corrections; the local Lean harness is a source-definition reproduction. Please rebase the root-physical wrapper on the corrected 438/909-step monitors rather than trying to salvage the 119-step statement.

The existing targeted run 43310306538 is failed at the compile step; I did not retrieve its logs. The mathematical counterexample above is independent of that run status.
