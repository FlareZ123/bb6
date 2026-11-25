# Champion score threshold for the Raw121 + Raw110 roster

## Claim

The exact champion score satisfies the stronger inequality

`2^63 ≤ proposedTM63Moves + 7`.

In particular,

`6766859 ≤ proposedTM63Moves + 7`.

The theorems are `BB6.Agent38ChampionThreshold.champion_score_ge_pow63` and `BB6.Agent38ChampionThreshold.champion_score_ge_6766859` in [ChampionScoreLowerBound.lean](ChampionScoreLowerBound.lean).

This is the numerical interface required to consume the source-certified Raw110 parent cover, whose exact target bound is 6,766,859, alongside the Raw121 parent cover. It does not establish any of the 70 remaining quotient Covers and is not a BB(6) upper bound.

## Proof

Only the first proposed source increment is needed. At the initial S1 state its parameters are `(m,n,a,b)=(2,7,6,63)`, and the proposed cost contains the term `42·2^63`. The inequality `14 ≤ 2^63` is kernel-decided; the remaining arithmetic proves that this first increment already exceeds `2^63`. The recursive `sectionResult` cost begins with this increment and adds only natural-number costs. Finally, the three-section composition includes the complete first section, and `threeSectionMoves_root` identifies that composition with `proposedTM63Moves`.

No enormous recursive score is unfolded or evaluated. The proof does not depend on a decimal expansion of the champion runtime.

## Integration

The champion-independent roster should remain separate from this score-specific fact. The intended consumer is the existing `Canonical70Raw121Raw110RosterOnly.exact_at_target`, instantiated at `B = proposedTM63Moves + 7` with the exact raw champion witness from `TM63RawUpperInterface`.

The appropriate acceptance target is the existing manual `canonical70` target in `.github/workflows/agent47-raw114-graft.yml`; this result does not justify a new workflow. Include this file as an additional source root and audit both printed axiom profiles.

## Verification boundary

The source is written against the repository's Lean 4.36.0-rc2 definitions and imports `TM63RawUpperInterface`. Local Lean execution was blocked in this invocation by a tool-level `ClientError` before the shell command ran. Therefore this file is a proof draft until the existing source-closure audit compiles it. The theorem contains no admitted proof or computational oracle by construction; its actual transitive axiom profile must still be confirmed by Lean.
