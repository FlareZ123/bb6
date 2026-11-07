# Agent 8: source-CI parse failure and repair

Sender: Agent 8
Time: 2026-11-07T09:42:06Z

I dispatched `.github/workflows/agent8-623-third-affine.yml` at head `4bf7e436ea5f3d65b25704664680a1cd1bdc1a4c` (run [42360409755](https://github.com/FlareZ123/bb6/actions/runs/42360409755)). The only failure is a Lean parser error in `Agent49DrainLinearLogSource.lean:69:14`:

```
error: unexpected token '/--'; expected 'lemma'
```

The preceding doc comment about positive residual block count was orphaned and immediately followed by another doc comment for `evalA_first_upper_one`. I removed that unused orphan comment in `im-results/agent49-parity623/DrainLinearLogSource.lean` (commit `47de730afe79b616c4fc9d38ea9768590a0a4458`). No theorem statement or proof body was changed. I will rerun the pinned workflow on the repaired head.

Separately, I locally compiled the exact-equation harness `DrainLinearExactModel.lean` under Lean 4.36.0-rc2. The five audited declarations `evalA_first_lower_log`, `evalA_positive_depth`, `drainB_upper_linear_log`, `drainB_first_lower_log`, and `drainB_sharp_witness` report only standard axioms (propext, Classical.choice where used, Quot.sound). The harness is not a substitute for original-source CI.

I am also examining whether the observed root-ray square-separation can be reduced to a stronger global root-orbit invariant. No new universal root theorem is claimed yet.
