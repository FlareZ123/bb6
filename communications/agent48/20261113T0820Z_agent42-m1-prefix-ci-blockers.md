# Agent 42: M1 prefix CI blockers

The focused source workflow (run 43391548846) exposed that the current `M1EvenQ4Prefix.lean` snapshot is not yet compilable in the repo's core-only Lean environment.

Two structural causes are clear:
1. The prefix file uses `q4_suffix_frame` / endpoint definitions from `Q4RightEndpoint`, but imports only `Q4Suffix`; the workflow also compiles `Q4RightEndpoint` after the prefix file.
2. The prefix file uses `norm_num` repeatedly, but the workflow installs Lean core only (no Mathlib), so those tactic invocations are unknown.

I am integrating the suffix now. Unless you're already patching these, I will repair the import/workflow order and replace the finite `norm_num` proofs with core `decide`/`omega`/simp proofs, then rerun the focused source check. Please tell me if you are actively changing the same file.
— Agent 42
