# Conditional non-coalescence of four authentic Cryptid-D root paths

## Result

For the four source-connected blank starts represented in the repository as D3, D0, D2, and D1 (control-state indices 3, 0, 2, and 5), the original-source section dynamics admit a uniform all-depth separation theorem.

For each root (r), assume that its authentic blank-start configuration does not halt. Then, for every finite return depth (k), there exists a nonhalting one-sided F/0 section whose arithmetic measure lies on a `Path135` path of length (k) from that root's certified anchor.

Moreover, if two such paths start from different root ordinals, or have different return depths, their unary section lengths are unequal. In particular, under the four nonhalting hypotheses, no two distinct root/depth pairs can coalesce at the same unary section length, regardless of how far the paths are followed.

This is an all-time conditional statement. It is not a proof that any of the four roots is nonhalting, nor a proof that any of them halts.

## Exact quantitative relation

For a section with unary length (n) and suffix length (L), the edge relation `Edge135` requires
[
8n le 3n' + 23,
qquad
3(n' + L') le 8(n+L) + 135.
]
The source adapter constructs each edge from the original-machine first-event theorem and the exact section encoding. Thus these are not bounds inferred from a finite simulation.

The four blank starts are connected to the arithmetic anchors by source-level prefix and halting-equivalence theorems:
- D3 (state index 3) to anchor 0;
- D0 (state index 0) to anchor 1;
- D2 (state index 2) to anchor 2;
- D1 (state index 5) to anchor 3.

The proof then combines:
1. the original-source one-sided halt-or-return theorem for arbitrary finite suffixes;
2. the exact `sourceSection` / `OneSided.Section` identification;
3. the source-derived `Edge135` section bounds;
4. the four exact blank-root-to-anchor correspondences; and
5. the arithmetic `disjoint_paths` theorem.

## Formalization and audit

The principal declarations are in:
- `im-results/agent36-cryptid-trace/SourceSectionBandsAdapter.lean`
- `im-results/agent36-cryptid-trace/FourRootSectionPath.lean`
- `im-results/agent36-cryptid-trace/FourRootAnchorSource.lean`
- `im-results/agent36-cryptid-trace/SectionBandSeparation.lean`

The integrated manual workflow `.github/workflows/agent32-cryptid-padding.yml`, target `four_root_anchor_bridge`, completed successfully in run `45449560801` (head `0344a3e6`). Its axiom audit reports:
- `exists_path_of_nonhalting` and the four root path theorems: `propext`, `Classical.choice`, `Quot.sound`;
- `source_paths_disjoint`: `propext`, `Quot.sound`.

There is no `sorryAx` in these audited declarations.

## What remains open

The theorem does not resolve the nonhalting hypotheses. The outstanding BB(6) question is still whether the authentic blank-start trajectory reaches a halting section, or instead continues through infinitely many returns. The result rules out a particular shortcut—coalescence of the four conditional root paths—but does not provide a universal upper bound or an exact Busy Beaver value.
