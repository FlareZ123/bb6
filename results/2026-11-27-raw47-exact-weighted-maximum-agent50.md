# Exact weighted maximum 143,977 for the Raw47 seven-hole parent

**Theorem (source-accepted).** Let `p` be the six-state, two-symbol partial table

```text
1RB---_1RC---_0RD---_1LD0RC_------_------
```

with seven unassigned transition slots. Under the repository's blank-start `WeightedBound` convention, the sharp universal bound for compatible total six-state machines is **143,977**. In particular, this is a result about the entire cylinder of `25^7 = 6,103,515,625` physical completions, not an experiment on one machine.

The exported Lean theorem `BB6.Agent50Raw47Complete.exact_threshold` states

```lean
theorem exact_threshold (B : Nat) :
  (∀ m, compatible parent m → WeightedBound B m) ↔ 143977 ≤ B
```

Here `parent` denotes exactly the partial table above. Its universal upper-bound half is also exported as

```lean
BB6.Agent50Raw47Complete.cover :
  Cover (WeightedBound 143977) parent
```

and `BB6.Agent50Raw47Complete.all_quotient` gives the analogous quotient-compatible statement. These are complete local statements without unresolved machine assumptions.

## Proof construction

The checked canonical depth-three quotient analysis partitions Raw47 into **1,212** residual cylinders. The source-accepted `Raw47Accepted1211` theorem removes **1,211** of these under weighted threshold **10,006**. It leaves one exact residual, indexed 61, with partial table

```text
1RB1LA_1RC---_0RD0LE_1LD0RC_0LA---_------
```

The independent `Raw47Late61Parent` theorem certifies that every completion of this remaining residual obeys weighted threshold **143,977**. Its difficult leaf has a verified **143,975-ordinary-move** trace reaching a halting query. The attaining completion has incoming blank delay **1**, so its weighted score is `143975 + 1 + 1 = 143977`. The trace proof uses checked block-transfer rules over arbitrary untouched tape tails, followed by a checked 2,741-command macro sequence and exact cost arithmetic.

The final `Raw47Lifted1212.remaining_count` kernel check proves that deleting this final certified parent leaves **zero** residuals. `Raw47Lifted1212.local_sound` composes the low-bound certificates and the late parent bound, while `Raw47Complete.cover` transfers the empty-residual quotient result to ordinary compatible machines. The separate attaining witness provides the matching lower bound.

This distinction matters: the theorem fixes the **weighted maximum** at 143,977; it does not separately assert that the maximum number of ordinary steps among this family's halting machines is 143,977.

## Source acceptance and reproducibility

The full original-source Lean 4.36.0-rc2 proof closure passed GitHub Actions [run 46068688341](https://github.com/FlareZ123/bb6/actions/runs/46068688341), source revision `5bd193066b82be12e3fa5e1e74477a3ff3ca5193`. The accepted artifact is `raw47-lifted1212`, artifact ID **15232511020**, archive SHA-256

```text
bfb3faae9359044ae0ebf1c233ec23f68d63cfee18e19dfb8db8cd584ca479c8
```

The successful workflow verifies the theorem and transitive axiom profiles for `Raw47Lifted1212.remaining_count`, `Raw47Lifted1212.local_sound`, `Raw47Complete.all_quotient`, `Raw47Complete.cover`, `Raw47Complete.cover_at`, `Raw47Complete.attained` and `Raw47Complete.exact_threshold`. Each passed the permitted profile gate: only `propext`, `Quot.sound` and `Classical.choice` may occur; `sorryAx` and unapproved axioms are excluded.

Two independently accepted inputs were imported, not rerun:

- [Run 46056674185](https://github.com/FlareZ123/bb6/actions/runs/46056674185), `raw47-accepted1211` (1,211 low-bound certificates), artifact 15226844140.
- [Run 46033320715](https://github.com/FlareZ123/bb6/actions/runs/46033320715), `raw47-late61` (single exceptional parent, attaining trace), artifact 15215900592.

The maintained source modules and proof templates are in [`im-results/agent50-raw47-depth3/`](../im-results/agent50-raw47-depth3/). The existing manual workflow [`.github/workflows/agent50-raw47-lifted.yml`](../.github/workflows/agent50-raw47-lifted.yml), `mode=lift`, `base_run=46056674185`, `base_count=1211`, `late_run=46033320715`, reconstructs the proof closure and exports the certified artifact.

## Exact scope within BB(6)

This result closes the Raw47 root cylinder. It is **not** a proof of the exact value of BB(6), nor an exhaustive upper bound over all six-state machines. The strongest independently accepted global interface at the time of this result is the conditional **Canonical41** roster at common floor 6,766,859. A separate original-source membership and consumption check must establish whether Raw47 is one of those 41 retained representatives. That computation was dispatched as [run 46069652144](https://github.com/FlareZ123/bb6/actions/runs/46069652144); until that run passes, the global roster count remains 41.
