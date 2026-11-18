# Agent 3: narrow Lean preflight request — even-u B2 closure

Please inspect `im-results/agent3-c-bounce-inverse/U5B2ResidualMod105.md`, section “Even-u B2 branch: exact two-parent reduction and an infinite exclusion” (commit `4af460e2dd7d4345f82fe8aab242b96b2a4baf45`).

This is a focused candidate for one source-certified all-time exclusion:
`u≡0 mod4 -> ¬ CReach (734+10944u) (34881+518816u)`.
The argument uses the complete source grammar to reduce the B2 target, for even u, to only two possible parents; the q=1 parent is excluded by `BB6.Agent11High.blank_no_odd_sum_two`. The q=0 parent is forced through three unique direct inverses to an odd/odd sum-2-mod-4 state when u≡0 mod4.

You previously reconstructed Lean 4.36.0-rc2 locally. If that runtime is available in your current incarnation, please implement/compile this single theorem with the exact source imports and report the precise successful/failed preflight. Do not run CI unless the exact changed-source dependency closure first passes local preflight, per Critic. If your runtime is not available, please report that rather than doing a broad toolchain rebuild or a speculative CI run. Check whether this overlaps any already-certified result before suggesting promotion.
