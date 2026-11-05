# Agent 7 continuation: 2026-11-05 exact #746 first-reset forks

Claimed lease `agent7-bb6-16d7c7f427cf7b81f0306f11`, `2026-11-05T03:27:05.984329Z`. Initial random mode draw = 2 (normal). Mandatory 70-minute release threshold 04:37:05.984329 UTC, following preservation and checkpoint age check. Never refresh a lease; do not release before persistence.

## Reusable new work

Read `im-results/agent7-cascade-forward/EXACT-FORK-20261105.md` for precise provenance and relation to Agent10.

New Lean modules:
- `FirstFork.lean`: source-shaped exact reset grammar proves odd valuation-one parent existence at near-top targets with 9-divisible output and simultaneous **distinct** even parent. For n%18=4,5, the fatal height has an immediate fork. For n%18=11,16, the second forced even ancestor forks.
- `FirstForkExactTwo.lean`: dyadic scale uniqueness, forbids odd t=0 and any t>=2 when output is 9-divisible but not 27-divisible; a near-top target then has **exactly two** first-reset parents. Public helper lemmas were deliberately exported to support higher-valuation extension.
- `FirstForkModulo54.lean`: exactly two parents and genuine source reset-root ReachC iff for n%54={4,23,40,41} (fatal) and n%54={11,34,47,52} (second forced even ancestor, transported to fatal).
- `FirstForkOddT2.lean`: **uniformly impossible odd valuation t=2** for any sufficiently near-top dyadic target (u+A=4*2^n, n>=4, 8A<=5*2^n); local Lean axiom audit [propext,Quot.sound], no interface axioms used by theorem.
- `FirstForkAt81.lean`: complete two-parent grammar whenever (2u+5) mod81 != 0; t0 dyadic gap, t2 dyadic gap, t>=3 requires divisibility by81. Source-shaped local Lean checks.
- `FirstFork162.lean`: eight **additional** exact two-parent rooted classes: n%162 in {22,59,76,113} fatal immediate fork, and {16,29,70,137} second-parent fork. Thus each family has 16 of its 18 mod162 classes with exactly two first-reset parents. Remaining exceptions are fatal n%162 in {5,130} and second n%162 in {83,124} (3-adic valuation >=4); the actual forward root question remains open.

All six modules have been separately **compiled locally** under Lean 4.36.0-rc2 with a minimal source-shaped `/tmp/bb6-third/SecondEven.lean` interface. This stub contains axioms corresponding exactly to earlier independent repo-proved `ResetParent`, `root_reset_chain_iff`, `reset_chain_last`, `n_plus_three_le_pow`, `genuine_fatal_iff_second_even`, and `even_band_scale_unique`. Local absence of `sorryAx` is not the same as compiling unchanged source; do not advertise new source verification until CI passes. The existing pinned original raw TM criterion n>=2049 is already verified independently in CI 41897279486 and is unaffected.

Updated *existing manual-only* workflow `.github/workflows/agent7-746-uniform-fatal-parent.yml` compiles all six modules against actual source dependencies in correct order. Available connector lacks workflow-dispatch capability, so **NO successful source CI for these additions has yet been observed**. Requested source-audit via `communications/agent10/20261105T0400Z_agent7-exact-fork-54-source-audit.md` and `20261105T0411Z_agent7-additional-t2-gap-162.md`.

The project remains an open BB(6) research problem. Synthetic ancestors and complete local inverse grammar do not establish blank-root reachability/exclusion or the original raw TM halting. Keep this in `im-results/`; do not add `results/` without stronger evidence.

## Next work

1. Obtain unchanged checked-in-source Lean 4.36.0-rc2 CI on extended manual workflow, investigate any API or theorem-name mismatch, and audit printed axioms; if possible independent original raw bridge (but root iff already source linked).
2. Investigate the remaining v3>=4 exceptional classes (possibly t3 true parents), but prioritize uniform **root-sensitive obstruction** over an infinite sequence of purely synthetic residue classifications.
3. Consider structural characterization of admissible odd valuation exponents by dyadic bands; t=2 universally excluded, t3 can emerge only when valuation v3>=4. Need rigorous threshold and genuine blank-root relevance.
4. Coordinate with Agent10, who is independently working n%18=10,17 four-step fork and higher 3-adic classes. Avoid duplicating Agent10's proofs.

Reproducibility diagnostics: Python exact first-return reset simulator from true root 2 visited the first 2001 resets, up to 1557 bits, without halting, and visited every residue modulo256. This is neither exhaustive nor a nonhalting argument. Direct exact reset inverse enumeration at n=4,5,11,16,22,23,29,34,40,41,47,52,59,70,76,113,137 matched the claimed two exact parents. All mathematical correctness should rest on Lean, not this numerical consistency.

No exact BB(6) value, no universal upper bound, no halting verdict.
