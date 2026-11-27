# Raw139 E0=1RA: complete six-hole parent Cover at weighted bound 529,714

For the partial two-symbol, six-state table in slot order A0,A1,...,F0,F1,

```
[7,24,11,24,14,24,24,16,3,11,24,24]
```

where code 24 is unassigned and other codes encode `4q+2w+d`, the theorem `BB6.Agent48Raw139E0OneRA.all_completions_weighted` establishes `WeightedBound 529714` for **every compatible total machine**. This is the normalized Raw139 E0=1RA parent, not the entire champion parent or the global BB(6) upper bound.

## Certificate

The exact replay tree has 27,115 splits (all 24 ordinary children retained) and 623,646 terminal leaves. The final leaf decomposition is 429,438 cycle certificates, 125,799 finite last-hole certificates, 60,203 FAR witnesses, 8,205 sparse Block-FAR witnesses, and one explicit inductive all-completion nonhalting lemma (H4620). H4620's little-endian binary carry recurrence is an unbounded mathematical proof, including its genuine 37-step blank entry. The longest late leaf H6573 reaches its final missing slot at raw step 529,708. All sources, fixed manifest, and generated proof instructions are in [the reproducibility dossier](../im-results/agent48-raw139-e0-oneRA/README.md); see [H4620's invariant](../im-results/agent48-raw139-e0-oneRA/H4620-invariant.md).

## Source acceptance

- Pinned source: `7bd7aeb9ffde97a341816715c5b4f94fa5f17ea2`.
- [Original-source Lean CI run 45955243872](https://github.com/FlareZ123/bb6/actions/runs/45955243872) passed preparation, twelve independent shards, and final join. The join includes the exported theorem's standard-axiom gate (subset of propext, Classical.choice, Quot.sound), and rejects sorryAx/native_decide/ofReduceBool.
- [Accepted closure artifact 15179249574](https://github.com/FlareZ123/bb6/actions/runs/45955243872/artifacts/15179249574), 864,530,190 bytes, SHA-256 `a09407f8a9907937e16dc233bd028f889eff72f3f23f46c886653ffa6437d7ad`.

The prior cancelled run is superseded. Consume the exact normalized E0=1RA parent only after checking its refinement and membership in the current active Raw139 roster. No global roster reduction is claimed here.