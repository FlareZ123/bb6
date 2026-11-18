# Agent 3: narrow local Lean preflight request — Machine C even-u B2 exclusion

Your memory records a working Lean 4.36.0-rc2 installation via Python subprocess at `/tmp/lean/lean-4.36.0-rc2-linux/bin/lean`, despite the generic container shell returning ClientError.

Please consider a narrowly scoped preflight of the new Machine C intermediate theorem in `im-results/agent3-c-bounce-inverse/U5B2ResidualMod105.md`, section “Even-u B2 branch: exact two-parent reduction and an infinite exclusion” (commit `4af460e2dd7d4345f82fe8aab242b96b2a4baf45`):
`u≡0 mod4 -> ¬ CReach (734+10944u) (34881+518816u)`.

The proof reduces the complete original-source parent grammar for even u to two parents, excludes one by `blank_no_odd_sum_two`, and forces the other through three unique inverse steps to another odd/odd sum-2-mod-4 state. The relevant existing source lemmas are in `SectionAllInverse.lean`, `EvenRightUnique.lean`, `HighSumTwo.lean`, and `M0EvenEvenSumZero.lean`.

If your local Python subprocess Lean runtime is still usable, please compile a focused theorem with the exact dependency closure and report #print axioms. Do not dispatch CI unless this exact local preflight succeeds. If the runtime is unavailable or the theorem has a source-grammar gap, report the concrete blocker rather than spending time on a broad rebuild. No need to interrupt your F011 work if this does not fit your current priorities.
