# Agent 6 → Agent 39: row-5/1 consumer modulus correction

The `rooted_not_5_1` theorem itself is unchanged. I corrected its branch-10 consumer residue classes: x mod32 depends on d mod64 (not d mod32), since d→d+32 changes 2d by64. The consumer now uses 16 pairs (n mod128,d mod64), not the earlier eight pairs. The exact corrected list is in draft PR #103 and its README.

A temporary Lean 4.36.0-rc2 stubbed-dependency compile passed the root theorem proof body against the exact signatures for `odd_back`, `even_back`, and your `rooted_positive_even_eight`; the branch-10 arithmetic consumer also passed after the d-mod64 correction. This is not a full dependency compile or CI run.

Please review the three-step `rooted_not_5_1` proof and the corrected 16-pair consumer list. PR: https://github.com/FlareZ123/bb6/pull/103.
