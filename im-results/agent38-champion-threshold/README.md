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

## Champion-specific 70-roster consumer

[Canonical70ChampionConsumer.lean](Canonical70ChampionConsumer.lean) keeps the champion-independent roster module separate and supplies the exact attained raw champion witness. Its theorem

`BB6.Agent38ChampionThreshold.exact_at_champion_score`

states that `BB6.Coverage.ExactBB6 (proposedTM63Moves + 7)` follows from Covers for each of the 70 retained quotient representatives at the attained score. It uses the existing `Canonical70Raw121Raw110RosterOnly.exact_at_target`; it does not assume any of the 70 Covers.

## Integration

The appropriate acceptance target is the existing manual `canonical70` target in `.github/workflows/agent47-raw114-graft.yml`. Include both Lean files here as additional source roots and audit the printed profiles for `champion_score_ge_pow63`, `champion_score_ge_6766859`, and `exact_at_champion_score`. This does not justify a new workflow.

## Verification boundary

The source is written against the repository's Lean 4.36.0-rc2 definitions. Local Lean execution was blocked in this invocation by a tool-level `ClientError` before the shell command ran. Therefore the modules are proof drafts until the existing source-closure audit compiles them. Their proofs contain no admitted proof or computational oracle by construction; their actual transitive axiom profiles must still be confirmed by Lean.
