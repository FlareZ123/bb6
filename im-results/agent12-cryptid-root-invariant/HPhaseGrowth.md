# Historical H-phase growth loop (withdrawn under source-correct DR branch)

**Status: WITHDRAWN as a source-stack identity.** The projected successor omitted the pinned source's DR right-head-one token branch. A corrected replay of the claimed 76-step CR macro invokes that token closure and does not reach the stated endpoint. Preserve this file as a historical abstract experiment only. See [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

## Entry into the loop

The previous version claimed that the root reached H(7) at outer index 21,926 and later reported a corrected prefix through macro 22,083. All of those macro indices are withdrawn: the outer DR successor omitted the source r1=1 token branch. The correct root starts with the 19-raw-step closure to CR([0,0,1],[1]) and then follows the candidate 7-closure recurrence in [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

The 157-successor H(7)-to-C1 entry was computed with the defective successor and remains unverified: the corrected interpreter reaches an unresolved token-normalizer case at outer step 11. The 76-successor C1 growth identity is falsified by corrected replay, which invokes the source-required DR right-head-one token closure and misses the claimed endpoint. The earlier claim that the blank-root seed reaches Corr(3,3) after 24 outer successors is withdrawn.

Set

```text
P = [0,0,1,0,19]
B = [0,0,0,2,0,0,0,2,0,0,0,16]
U = [0,0,0,12,0,0,0,12,0,0,0,12,0,0,0,2,0,0,0,0]
```

The old simulator claimed the following 157-successor H(7)-to-C1 entry (not source-validated):

```text
S^157(H(7)) = CR(L=[1,0], R=P ++ B ++ U).
```

This was a state-level identity in the old simulator only. Neither the entry from H(7) nor the reported macro-22,083 root state is source-valid.

## Historical 76-successor growth claim (falsified)

For every finite list suffix `T`,

```text
S^76(CR(L=[1,0], R=P ++ B ++ T))
  = CR(L=[1,0], R=P ++ B ++ B ++ T).
```

This claim is not source-valid. The old successor's zero-token-call count was incomplete because it treated DR right-head 1 as an ordinary transition. Under the corrected r1=1 token branch, replay invokes a token closure and does not reach the claimed endpoint.

The claimed C_n infinite-orbit conclusion is withdrawn. The corrected replay does not establish S^76(C_n)=C_(n+1), so no infinite orbit follows from this macro.

## Source corrections and invalidated root claims

The token-normalizer corrections in [TokenNormalizerCorrection.md](TokenNormalizerCorrection.md) remain useful. However, all root states reported from the old simulator, including the macro-21,810 token event and the claimed H(7) entry, are withdrawn because the outer DR r1=1 branch was omitted. The corrected first root closure and candidate recurrence are documented in [DRHeadOneCycle.md](../agent48-cryptid-root-cycle/DRHeadOneCycle.md).

The former claim that the 76-step identity makes zero token-normalizer calls is invalid: the old simulator did not classify DR right-head 1 as a token branch. The corrected replay invokes a token closure and misses the claimed endpoint. Neither the standalone identity nor root reachability is currently established.

## Reproduction and evidence

Agent 32's earlier entry and tail-sentinel checks exercised the defective projected successor. A replay with the corrected r1=1 branch fails the claimed 76-step endpoint and invokes a DR token closure. Those earlier checks are historical simulator evidence only, not source correspondence.

## Current formalization target

The previous formalization argument is withdrawn. The 76-step C1 replay enters the r1=1 DR token branch and misses the claimed endpoint; the 157-step H(7)-to-C1 entry remains unresolved because the corrected interpreter stalls in a token-normalizer case. The only current formalization target is the 19-step DR-to-CR root closure and 36-step CR recurrence in DRHeadOneCycle.md.

The remaining obligation is to formalize the candidate 36-raw-step recurrence and its 19-step root entry against the pinned source, then compose with the existing seven-step blank-root entry. Until that compiles, the nonhalting conclusion remains a proof target.

Until the new recurrence is compiled and its source correspondence is established, **do not claim the original TM is nonhalting**. This historical H-phase experiment establishes neither a source-valid infinite orbit nor a BB(6) result.

## Historical raw-step accounting (invalidated)

The 254-step total below belongs to the old projected path and is not a source-valid raw execution.

## Raw TM cost of the 76-step macro

Agent 32 matched the 76 outer branch labels to the exact `execute n` lengths in the external #85 mode-closure proof. The branch accounting is:

| branch | occurrences | raw TM steps each | subtotal |
|---|---:|---:|---:|
| CR L=1, second=0 (`CR10`) | 8 | 5 | 40 |
| CR L=1, empty tail (`CR1e`) | 1 | 6 | 6 |
| CR L=1, second=1 (`CR11e`, `CR11`) | 2 | 16 | 32 |
| CR L=0 (`CR0`) | 13 | 2 | 26 |
| EL R=0 (`EL0`) | 16 | 2 | 32 |
| EL R>0 (`EL+`) | 12 | 1 | 12 |
| DL R=0 (`DL0`) | 8 | 6 | 48 |
| DL R>1 (`DL+`) | 4 | 4 | 16 |
| DR L=0, R>0 (`DR0+`) | 8 | 4 | 32 |
| DR L>0, R>0 (`DR++`) | 3 | 3 | 9 |
| DR L empty (`DRempty`) | 1 | 1 | 1 |
| **Total** | **76** |  | **254** |

The 254-step total is bookkeeping for the invalid old projected path. The claim that the path enters no token-normalizer branch is false under the pinned source and must not be used.

The following was Agent 32's proposed direct formalization target for the now-withdrawn macro; it should not be used:

`evalStackCfg .CR_n_n [(1,0),(0,0)] (P ++ B ++ T)`

to

`evalStackCfg .CR_n_n [(1,0),(0,0)] (P ++ B ++ B ++ T)`

by `execute 254`, for arbitrary finite suffix `T`. This may avoid depending on private #85 `mode_*_closed` lemmas: prove the complete raw run in the #490 namespace using its public `execute` semantics and endpoint encodings. If one 254-step proof is unwieldy, split it into the 76 branch runs.

Source proof route: the #85 branch proof block is at lines 901–1065 of the external source file; branch counts and durations above were extracted from those `execute n` calls. This is a proposed Lean proof route, not yet a compiled theorem.