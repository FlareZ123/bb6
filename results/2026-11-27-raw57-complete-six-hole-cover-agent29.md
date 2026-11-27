# Source-accepted six-hole Raw57 parent Cover at weighted bound 1613

**27 November 2026. A complete local classification; not a proof of BB(6).**

## Statement

Under the repository's standard six-state, two-symbol Turing-machine convention, let the partial machine (p_{57}) be given by

```
1RB---_1RC---_0RD---_1LD1RE_---0LA_------
```

(12 transition slots, six assigned and six initially undefined). Its free slots admit exactly **25⁶ = 244,140,625** literal total completions, including the halting choice in each slot.

The following theorem was compiled and accepted from original source in Lean 4.36.0-rc2:

```lean
BB6.Agent31Raw57.literal_cover :
    Cover (WeightedBound 1613) BB6.Agent31Raw57.literalParent
```

This is a **universal** boundedness assertion for every total completion compatible with (p_{57}), not a finite simulation on selected machines. The `WeightedBound` interface includes the repository's first-one/zero-prefix delay convention, so it is strictly the property stated by the formal theorem. The bound **1613 is sufficient**, not claimed optimal.

The proof's essential source is `im-results/agent1-raw57/Raw57ParentComplete.lean`, exported through `Raw57ParentCover.lean`. It composes the original-source parent split over the first undefined transition with the five nontrivial sibling bounds, including the 1LA and 1LE branch certificates and the 1LB, 0LF and 1LF source-certified branches. Remaining first-split choices are discharged by explicit terminal or regular nonhalting evidence. Its final statement is not conditional on any unresolved sibling.

## Reproducible source acceptance

| Requirement | Accepted evidence |
| --- | --- |
| Lean toolchain | 4.36.0-rc2 |
| Final CI run | [46074414244](https://github.com/FlareZ123/bb6/actions/runs/46074414244) (success) |
| Published proof archive | [artifact 15234538009](https://github.com/FlareZ123/bb6/actions/runs/46074414244/artifacts/15234538009), `raw57-prefix-parent-certified` |
| Artifact archive SHA-256 | `412a081a140441aea6979879e8347976dfb38eb8544661f9a815b9ded77c973e` |
| Lean source closure | 14,551 project modules from the complete final parent root |
| Explicit axiom audit | All 55 reported theorem profiles use only `propext`, `Classical.choice`, `Quot.sound`; neither `sorryAx` nor `native_decide` is accepted |
| Final theorem | `BB6.Agent31Raw57.literal_cover` |

The final source assembly is reproducible through `im-results/agent1-raw57/recover_rc2.py` and the manual `.github/workflows/agent29-raw57-resume.yml` with `assemble_only=true`. It authenticates previously accepted original-source shard objects **0–17** from [run 46035478679](https://github.com/FlareZ123/bb6/actions/runs/46035478679) and shard **18** from [run 46064160509](https://github.com/FlareZ123/bb6/actions/runs/46064160509), then compiles the corrected **1613** final consumer sources after all shard source hashes are checked. This reuses the already checked expensive proof material without relaxing source identity, object identity, or axiom conditions.

A repaired final interface was necessary because an earlier thin consumer expected an obsolete 832-weight branch type; this was an interface inconsistency, not a failed mathematical shard. The successful final assembly corrected it without rebuilding or altering accepted child certificates.

## Relevance to the global frontier

The theorem closes this complete six-hole **local** family. It is a valid input to the repository's quotient-roster elimination theorem, provided that the exact parent is proved to occur uniquely in the relevant accepted global roster. The accepted Canonical41 fixed-score theorem still has hypotheses for 41 residual parent Covers. The separate integration workflow [46075158700](https://github.com/FlareZ123/bb6/actions/runs/46075158700) was launched to verify Raw57's membership and transport its Cover into a candidate Canonical40 successor. **Do not infer Canonical40 is source-accepted until that integration passes.**

Neither the local Raw57 theorem nor the conditional Canonical41 interface determines the exact six-state Busy Beaver function, which remains open.
