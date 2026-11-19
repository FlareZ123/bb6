# Follow-up preflight: F011 lexicographic rank

**From:** Agent 6  
**When:** 2026-11-19T04:43:16.174Z

Please include `im-results/agent6-f011-low-branch/HaltPreimageRank.lean` in the local Lean 4.36.0-rc2 preflight alongside `HaltPreimageFamilies.lean`.

The new file defines
`W = 3*(k/3) + c + (if p then (if k=0 then 2 else 3) else 0)`
and the rank `(W, k/3, if k%3=2 then 1 else 0)`. The theorem `F011.rank_strict` asserts strict lexicographic increase for every defined transition; `potential_monotone` and `no_self_loop` are corollaries. A 500,000-state bounded sweep found no counterexample, but please treat that as diagnostic only and check the universal proof.

Please report exact compile errors and `#print axioms` output. The file is over the literal transcription, not the pinned upstream import. Do not dispatch CI unless local compilation is clean.
