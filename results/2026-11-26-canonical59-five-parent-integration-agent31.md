# Source-accepted Canonical59 five-parent reduction

**26 November 2026 — formal conditional result.** This result extends the accepted Canonical64 quotient interface by five independently source-accepted parent Covers. The exact residual obligation count falls from 64 to 59. It does not determine BB(6).

## Mathematical statement

Let `rosterSelected` be the quotient-compatible complement obtained by removing the following five pairwise-distinct parent machines from `BB6.Agent3Canonical64Raw120.roster64`:

| Parent | Exact source theorem | Weighted bound |
| --- | --- | ---: |
| Raw119 | `BB6.Agent10Raw119.all_completions` | 572 |
| Raw115 | `BB6.Agent47Raw115.all_completions` | 7,014 |
| Raw58 | `BB6.Agent4Raw58Exact.coverRaw58` | 3,055,746 |
| Raw108 | `BB6.Agent10Raw108Closed.all_closed` | 4,136,180 |
| Raw118 | `BB6.Agent1Raw118Complete.parent_cover` | 756,496 |

Each parent is an exact literal-table match and occurs exactly once in Canonical64. All five parent Covers are lifted to the common weighted floor 6,766,859. No candidate was rejected.

The generated Lean module is `CanonicalSelectedParentIntegrated.lean`, in namespace `BB6.Agent32CanonicalSelectedIntegrated`. Its kernel-checked declarations establish:

1. `countSelected : rosterSelected.length = 59`;
2. `raw59_retained`: the exact Raw59 table occurs exactly once in the remaining complement;
3. pairwise distinctness of the five removed parents;
4. their common root compatibility and Cover obligations;
5. `sound_integrated`, the weighted-TNF quotient reduction for the 59-member residual roster;
6. `exact_at_target` and `exact_at_champion_score`.

In particular, the fixed-score theorem has the form: if every one of the 59 retained representatives has a Cover at the attained champion score, then the named blank-start champion witness and the quotient reduction imply `ExactBB6` at that score. The common floor 6,766,859 is a reduction threshold, not a claim that the champion's exact score equals that number.

**The 59 residual Covers are still hypotheses.** This result is not a universal upper bound and does not establish the exact value of BB(6).

## Reproducibility and kernel audit

- Workflow run: [45880290680](https://github.com/FlareZ123/bb6/actions/runs/45880290680).
- Source revision: `bd64e66c5461f413150d62b6593aa9d071de85d4`.
- Lean toolchain: Lean 4.36.0-rc2.
- Base Canonical64 proof artifact: 15085029091.
- Generated source SHA-256: `38d00088a70b3f290651b40f5f1a4a5e691963c35b9f2c3372e80bfa0d6e80c3`.
- Generated OLean SHA-256: `213f1a6fa5fb7b53a92fbe8385130ef330476eab46e917cce0a4fe2d6a81cc9f`.
- Full linked proof-closure artifact: [15147189928](https://github.com/FlareZ123/bb6/actions/runs/45880290680/artifacts/15147189928), SHA-256 `f19b9977f3e3f3a60c49ae61ad4c5a717689980191bf7ee0d23e7eeff1c27abc`, 5,720,769,280 bytes.

The final theorem profiles use only `propext`, `Classical.choice`, and `Quot.sound`. The integration gate rejects `sorryAx` and `native_decide`. Raw118's source-accepted parent Cover and unique Canonical64 membership were independently checked before being recompiled in the joint environment; the other four parent proofs and their unique membership counts were likewise recompiled in that environment.

## Exact parent artifact pins

| Parent | Run / artifact | Artifact SHA-256 |
| --- | --- | --- |
| Raw119 | [45755653372](https://github.com/FlareZ123/bb6/actions/runs/45755653372) / 15087741037 | `b6997b8b530e59357bf8deabbc295f51f03b85567b99773b2fa91248ca3be235` |
| Raw115 | [45783903926](https://github.com/FlareZ123/bb6/actions/runs/45783903926) / 15100255568 | `a4eea4fe3327e993aa402544af9991e03faa56e9f04b3609a41e7f9ee615b453` |
| Raw58 | [45762057732](https://github.com/FlareZ123/bb6/actions/runs/45762057732) / 15090715339 | `2231c274970b233002894c3fa097e3b81ad1484a3db0809c0148f8c03e26c477` |
| Raw108 | [45788380944](https://github.com/FlareZ123/bb6/actions/runs/45788380944) / 15101731441 | `77f7274d51f16697b29bcf2fbee1eb25ed3a2084b1e5134e36bd6e3759e6d21c` |
| Raw118 | [45812415227](https://github.com/FlareZ123/bb6/actions/runs/45812415227) / 15120592642 | `226a16e1181a456a2f6eddfb785b3882abde05d462837fffcb4b3ba47dfe2053` |

Raw118's unique Canonical64 membership was separately accepted in [run 45845180631](https://github.com/FlareZ123/bb6/actions/runs/45845180631), artifact 15131232543. Its membership theorems were recompiled and included in the final joint axiom audit.

## Next mathematical obligation

The remaining task is not to repeat any of these five parent proofs. It is to establish additional exact parent memberships and Covers, or to resolve the 59 retained quotient representatives directly. Raw59 is deliberately retained here; its separate staged relocation/graft must pass its own strict source and kernel checks before any further count reduction is claimed.
