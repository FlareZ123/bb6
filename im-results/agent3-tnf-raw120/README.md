# Raw120 E0 sibling certificates

Parent: `1RB---_1RC---_0RD---_1LD1RE_---1LE_------`. First undefined row E0 at ordinary time 9.

## Accepted complete parent and exact weighted threshold (2026-11-26)

**All 25 disjoint E0 branches are source-accepted. The entire Raw120 cylinder has exact uniform weighted threshold 224707.** In [run 45733198942](https://github.com/FlareZ123/bb6/actions/runs/45733198942), both the 1LB child job 139620035429 and the complete parent job 139639329915 succeeded at revision `e8dbaab36366b8282388cff6eda45fb550372774`. The parent job composes all 25 choices (`Raw120Complete.allRaw120`, `coverRaw120`) and checks `Raw120ExactLower.raw120_lower`, which forces the bound 224707 from the attaining 1LB late leaf. It rejects `sorryAx` and `native_decide`. Artifact **15080392441** (`raw120-parent`, SHA-256 `617e0e6e523edfe5bdbba757d812e2139555f054e9d4a857ccfee54d685a2364`) contains the checked object closure and manifest. Thus every compatible machine satisfies the bound, and no smaller uniform weighted bound suffices. The six-hole cylinder has 25^6 = 244,140,625 raw completions; this is not a count of canonical machines. The exact parent has now been consumed in the source-accepted 64-representative quotient frontier described below.

| E0 | Weighted bound | Evidence |
| --- | ---: | --- |
| 0LC, 0LD, 0LE, 0RD, 0RE, 1LC, 1LD, 1LE, 1RD, 1RE | 0 | Raw120EasyCycles.lean; [45582268224](https://github.com/FlareZ123/bb6/actions/runs/45582268224) |
| Halt | 15 | Raw120ThreeResidual.lean, original-source local compile |
| 0LA | 18859 | [matrix job 139516363530](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363530); artifact 15067629775; [dossier](0LA-dossier.md) |
| 0LB | 520 | [matrix job 139516363493](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363493); artifact 15066016797; [dossier](0LB-dossier.md) |
| 0LF | 656 | [matrix job 139516363472](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363472); artifact 15071262082; [dossier](0LF-dossier.md) |
| 0RA | 3320 | [matrix job 139516363514](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363514); artifact 15064463097 |
| 0RB | 223 | [45532860093](https://github.com/FlareZ123/bb6/actions/runs/45532860093); matrix artifact 15067335440 |
| 0RC | 716 | [45584144941](https://github.com/FlareZ123/bb6/actions/runs/45584144941); matrix artifact 15066948489 |
| 0RF | 14416 (exact) | [45520792124](https://github.com/FlareZ123/bb6/actions/runs/45520792124); matrix artifact 15067684633 |
| 1LA | 13113 | [matrix job 139516363603](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363603); artifact 15070047501; [dossier](1LA-dossier.md) |
| 1LF | 1855 | [matrix job 139516363565](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363565); artifact 15071453743; [dossier](1LF-dossier.md) |
| 1RA | 13317 | [45685953381](https://github.com/FlareZ123/bb6/actions/runs/45685953381) |
| 1RB | 749 | [45584422715](https://github.com/FlareZ123/bb6/actions/runs/45584422715) |
| 1LB | 224707 (exact) | [dossier](1LB-dossier.md); [accepted repair job 139620035429](https://github.com/FlareZ123/bb6/actions/runs/45733198942/job/139620035429), artifact 15080541393 |
| 1RC | 135 | [matrix job 139516363381](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363381); artifact 15073891914 |
| 1RF | 889 | [matrix job 139516363775](https://github.com/FlareZ123/bb6/actions/runs/45702614303/job/139516363775); artifact 15076397787 |

All 14 successful matrix artifacts pin source revision `3a45edaf85bc519ee64e07f5b1379664b352a023` in [run 45702614303](https://github.com/FlareZ123/bb6/actions/runs/45702614303). Its sole cancelled child 1LB stalled during Python witness discovery, before Lean compilation. Both 1RC and 1RF final `allOneR*` theorems use only propext, Classical.choice and Quot.sound. The targeted repair reused the 14 accepted artifacts and reran only 1LB, checking all object/source hashes and shared dependency identities before successful parent compilation.

## Parent and canonical composition

- [Raw120Complete.lean](Raw120Complete.lean): accepted all-completions theorem at 224707 and Cover at every larger target.
- [Raw120ExactLower.lean](Raw120ExactLower.lean): accepted sharpness theorem using the exact 1LB late leaf 1341 (224705 live transitions, one halt tick, and one incoming blank-prefix step).
- [Canonical64Raw120Integrated.lean](Canonical64Raw120Integrated.lean): consuming theorem against Agent31's eleven-parent `Canonical65Integrated` environment from run 45732489302, artifact 15078085872. It tests exact membership and a one-entry removal, then imports the actual accepted Raw120 proof and composes both exactness directions. **Source-accepted** in [run 45750164590](https://github.com/FlareZ123/bb6/actions/runs/45750164590) at revision `949fde331f10df81a968f157c622faa581597276`. Artifact 15085029091 (SHA-256 `bb4fa3c190ab2a67e3f7c17f8e1c0f07c2215b282451a361501f8ff6c678d55b`) records the exact 64 count, `sound64_integrated`, and `exact_at_target`, with only standard axioms. The other 64 Covers and the champion witness remain explicit.
- Historical [Raw120ThreeResidual.lean](Raw120ThreeResidual.lean) and [Raw120Canonical76Graft.lean](Raw120Canonical76Graft.lean) preserve the earlier partial partition and conditional 76→75 mechanism; their remaining parent premise is now discharged by the completed Raw120 theorem. The current integration target is the eleven-parent environment, not a separate competing 75-entry roster.

The 0RF child alone disproves a uniform 7014 bound for raw120. The final roster composition must lift this parent bound to the champion score rather than impose 7014.

## Exact 0RF and 0RB certificates

All 25^5 = 9,765,625 raw completions of that child are accounted for by the exact first-hole enumeration: 1563 splits, 26299 cycle leaves, 5858 last-hole leaves, 3793 initially open leaves. The open-list SHA256 is bda880d33c84532152766ab55afccf0744461e91eb337a3badecb8719f1a68dc. Of the 3793, 3761 have FAR witnesses (29 reusable DFAs), 27 have one-block growth proofs, one has a two-block growth proof, three have new parametric invariants, and one halts. The exact weighted threshold for this child is **14416**.

The late table `1RB1LF_1RC1RF_0RD1RB_1LD1RE_0RF1LE_---0LA` reaches its only hole F0 after 14415 ordinary transitions with zero initial delay. Thus a blanket 7014 weighted bound for raw120 is false. This is not a new BB(6) lower bound competitive with the champion. Use the mixed-bound roster composition at the final champion bound, rather than require each residual to have bound 7014.

## Source-linked verification

The existing manual target `weighted-tnf-raw120-rf` passed in [CI run 45520792124](https://github.com/FlareZ123/bb6/actions/runs/45520792124), on source commit `72d380da6ee9062827a0df0fb4d7840cea88bec3`. Its dedicated `raw120` job regenerated the RF tree, compiled the source-linked dependency closure, and finished successfully. The closure compiled 79 project modules, including `Raw120Late`, the 24 generated RF child modules, and `Raw120RFData`.

The generated final theorems are:

- `allRF`: every machine compatible with the E0=0RF child satisfies `WeightedBound 14416`.
- `exactRF`: for every `T`, all compatible machines satisfy `WeightedBound T` iff `14416 ≤ T`.

The job printed the axiom profiles of `c_root`, `allRF`, and `exactRF`; each used only `propext`, `Classical.choice`, and `Quot.sound`. The workflow also rejects `sorryAx` and `native_decide`, and that guard passed. This is original-source Lean acceptance of the complete E0=0RF child certificate, not merely a local preflight.


### E0=0RB exact child result

The E0=0RB child is
`pRB := refine p120 (4,false) (some ⟨false,true,1⟩)`.
All 25^5 = 9,765,625 completions are accounted for by the pinned first-hole enumeration: 1095 splits, 17813 cycle leaves, 4766 last-hole leaves, and 2607 initially open leaves. The open-list SHA256 is `3de8ddb0bbf7be1fd2858ab0df342d7f2a40114cab76af3baeb36f64c13f4a2c`.

Of the 2607 open leaves, 2587 have FAR witnesses from `rb-bank.txt`; the remaining 20 are covered by 18 one-block sweep pumps and two multi-block growth proofs. One multi-block witness is the generated period-32 pump at open index 925 (parameters `(32,26,8)`); the other is the custom counter/pump for open index 973 in `Raw120RBCounter.lean`. The exact weighted threshold is **223**. The generator pins the open-list hash, open count, FAR count, symbolic witness indices, tree root, and full tree statistics before emitting Lean.

The generated theorem `allRB` proves that every machine compatible with this child satisfies `WeightedBound 223`. This is a source-checked upper bound for the entire E0=0RB cylinder, not just the enumerated sample.


The E0=0RB manual target `weighted-tnf-raw120-rb` passed in [CI run 45532860093](https://github.com/FlareZ123/bb6/actions/runs/45532860093), completing at 2026-11-25T02:53:42Z. Its dedicated `raw120` job regenerated the pinned RB tree and compiled the generated `Raw120RBData.lean` dependency closure. The generated file checks `c_root` and `allRB`; the workflow's source guard (which rejects `sorryAx` and `native_decide`) passed. The RB child is therefore accepted by original-source Lean CI.


## Reproduction

The manual workflow `.github/workflows/agent3-raw120-complete.yml` has a new `integrate-65` mode using the two pinned accepted parent/core artifacts, without regenerating any child. The earlier `repair-1lb` and `all` modes reproduce the parent proof; do not rerun them merely for integration. The child artifacts contain source/olean manifests; `assemble_shards.py` checks source revision, hashes and dependency identities before composition. The integration uses the existing Agent31 reached-kernel comparator and checks all exported axiom profiles.

The generators are generate.py (0RF), generate_rb.py, generate_rc.py, generate_la.py and generate_sibling.py. The individual dossiers preserve discovery details and candidate witness indices. The matrix consumes generated Lean proofs; no native decision oracle or sorry is needed.
