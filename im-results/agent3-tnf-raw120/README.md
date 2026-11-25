# Raw120 E0 sibling certificates

Parent: `1RB---_1RC---_0RD---_1LD1RE_---1LE_------`. First undefined row E0 at ordinary time 9.

## Accepted partial closure (2026-11-25)

**22 of 25 disjoint E0 branches are covered; three remain: 1LB, 1RC, 1RF.** The original-source Lean composition [Raw120ThreeResidual.lean](Raw120ThreeResidual.lean) imports nine successful matrix child artifacts and uses two previously accepted child bounds as explicit premises. It also proves the immediate-halt branch and ten translated cycles. It compiles locally against the original Lean 4.36.0-rc2 artifacts, with only standard axioms. Every covered branch satisfies WeightedBound 18859. The partition leaves exactly 29,296,875 raw completions, versus 214,843,750 covered; each child has mass 25^5 = 9,765,625. These are cylinder counts, not distinct canonical machines.

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
| 1LB | candidate 224707 | [dossier](1LB-dossier.md); aggregate matrix check pending |
| 1RC | pending | 3075 open leaves; 3048 FAR, 24 generic sweep, 3 custom witnesses (939, 1928, 1934) |
| 1RF | pending | Six bespoke original-source never-halting proofs compile locally; aggregate check pending |

The nine matrix artifacts above pin source revision `3a45edaf85bc519ee64e07f5b1379664b352a023`. The matrix run is [45702614303](https://github.com/FlareZ123/bb6/actions/runs/45702614303). Its generated modules and dependency identities support local composition without regenerating the enumerations. The earlier dedicated 1RF run [45699530786](https://github.com/FlareZ123/bb6/actions/runs/45699530786) failed; its job logs were unavailable (HTTP 404). Local generation and compilation of both Raw120OneRFCounter and Raw120OneRFRecursive against the original PhaseClosure artifact now succeeds for leaves 1658, 1676, 1677, 1678, 2120 and 2118. This is not yet aggregate sibling acceptance.

## Parent and canonical composition

- Raw120ThreeResidual.lean: pairwise disjoint remaining children, exact mass identities, parent_partition and cover_from_three. Its two explicit premises are the already accepted 1RA and 1RB bounds.
- Raw120Complete.lean: complete candidate parent composition at bound 224707, awaiting all three remaining aggregate certificates.
- Raw120ExactLower.lean: consumes the 1LB late leaf 1341, whose 224705 live transitions, halt tick and one incoming blank-prefix step give weighted threshold 224707. The exact parent lower bound still requires composition with the original-source late artifact.
- Raw120Canonical76Graft.lean: corrected thin consumer of the **accepted raw107+raw114 canonical76 roster**, not the different raw114+raw121 roster that also has length 76. Lean locally checks parent_present, roster75_count, roster75_sound and exact_at_target against canonical artifact 14997966221. Conditional on a full raw120 bound, precisely this roster drops from 76 to 75. The theorem explicitly retains all 75 other Covers and the champion witness. **No global roster entry is removed yet.**

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

Use the manual workflow `.github/workflows/agent3-raw120-complete.yml` for the full child matrix, or existing targeted manual jobs. Do not regenerate accepted siblings merely to inspect the remaining ones. The child artifacts contain source/olean manifests; `assemble_shards.py` checks source revision, hashes and dependency identities before composition.

The generators are generate.py (0RF), generate_rb.py, generate_rc.py, generate_la.py and generate_sibling.py. The individual dossiers preserve discovery details and candidate witness indices. The matrix consumes generated Lean proofs; no native decision oracle or sorry is needed.
