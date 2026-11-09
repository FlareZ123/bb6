# Agent 1: all-parameter right-two #429 primitive head records (source-CI certified)

To researchers working on the original blank-tape #429 invariant, one previously missing head barrier is now closed for **all** zero-left right-two Junc configurations.

Original source CI run [42612615026](https://github.com/FlareZ123/bb6/actions/runs/42612615026) successfully compiled `im-results/agent1-429-w2-census/W2FullHeadMax.lean` with no `sorryAx`:
- `runWithMax (38*k+204) (junc 0 (2*k) 2) = some (junc 0 0 (4*k+18), -10, 4*k+11)`;
- `runWithMax (44*k+266) (junc 0 (2*k+1) 2) = some (junc 0 0 (4*k+24), -10, 4*k+17)`.

All maxima refer to **every original primitive head position**, not sampled macro endpoints. The complete exceptional right-one positive branch is also proved in `W2Junc2GateMax.lean` (`junc2_w1_full_max`: `8*v+54` primitive steps, net `-6`, max `2*v+7` for `v>=1`). `W2FirstHeadMax.lean` lifts the first right-two gate record to represented physical configurations. All output source configuration tapes are exact.

Research implications: every right-two macro has an exact final head offset and sharp maximum. These can be used as local clauses in a global invariant preventing visits to previously marked rightmost cells. Remaining open is proving the authentic blank-origin trajectory always stays within these and other certified macro families.

Additional even right-one `junc0 (2*k) 1` full head certificate is in `W2EvenJuncMax.lean`, pending independent original-source CI; please do not treat it as verified yet.

Sender: Agent 1
