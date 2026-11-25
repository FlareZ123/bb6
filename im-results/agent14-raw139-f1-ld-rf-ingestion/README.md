# Raw139 F/1 = 1LD and 1RF ingestion

This is an intermediate source-reconstruction and frontier-consumer package. It does not belong in results/ and does not claim an exact BB(6) result.

## Existing mathematical certificates

| F/1 sibling | Exact parent | Weighted bound | Existing partition |
|---|---|---:|---|
| 1LD | [7,24,11,24,14,21,3,16,12,11,24,14] | 264 | 13 splits, 300 leaves: 170 cycles, 53 last-hole, 45 FAR, 32 inductive growth |
| 1RF | [7,24,11,24,14,21,3,16,12,11,24,23] | 5423 | 11 splits, 254 leaves: 136 translated cycles, 65 last-hole, 21 FAR, 29 affine growth, 3 recursive carries |

Both all-completion theorems were previously compiled locally against the hash-verified original-semantics dependency artifact from Agent48 run 45611897213. They have not yet had independent clean source-closure CI or canonical77 ingestion. Their exact theorem names are BB6.Agent14F1OneLD.all_completions_weighted and BB6.Agent14F1OneRF.all_completions_weighted.

## Purpose of this package

1. Deterministically regenerate the existing 1LD and 1RF Lean source modules and verify their committed SHA-256 values.
2. Compile both closures against the reusable Agent6 champion-residual core artifact.
3. Prove exact depth-five sibling identity and membership in the current 102-leaf raw139 frontier.
4. Remove only those two exact parents, preserve the complement, and expose the resulting conditional canonical77 exactness interface.

The intended arithmetic is 102 raw139 leaves to 100, hence 178 canonical77 obligations to 176. These counts are claims to be checked by Lean in the combined workflow, not assumed facts.

## Validation boundary

The workflow must report the four source-level all-completion theorems and all 32 1LD growth/never pairs, as well as the parent membership, count, cover, and exactness theorems. Accepted axiom profiles are restricted to propext, Classical.choice, and Quot.sound; sorryAx and native_decide are forbidden.

Even if the sibling graft succeeds, the remaining 176 obligations are not discharged here. The global BB(6) upper bound remains open.

A source-only CI mode is also available in the existing Agent6 workflow: dispatch with agent14_source_only=true and source_sha set to this branch commit. It downloads the accepted Agent48 artifact from run 45611897213 and independently audits the 1LD/1RF source closures, without waiting for the Agent6 champion core build. The full parent graft still requires the Agent6 core artifact.
