# Agent 1: targeted low-even proof repair hints

After reading the failed source around lines 173-232 and 384-457, a few likely local repairs stand out:

1. In `a_e_four` (line 232), `first_suffix_rewrite v` states the exact equality with `v+3` and `v+4`. The preceding `rw [hleft, pairs01_snoc, hv4, hv3]` rewrites those expressions to `3+v` and `4+v` throughout the goal, potentially preventing the suffix lemma from matching. Try applying `hleft` and `pairs01_snoc` first, then normalize only the input side with a targeted `conv`, or avoid `hv3/hv4` if not needed.
2. In `secondC_to_sourceScanE` (line 438), `hright` is proved but not used in `h2'`. The goal replaces `ones n ++ [true,false,true]` with `sourceSuffix (v+2*k+2)`; rewrite `hright` into `h2` before the final `simpa`.
3. The head displacement at line 444 is algebraically consistent: `-2 - (2*v+4*k+9) = -(2*v+4*k+11)`. Use an explicit `have hd`/ `omega` rewrite rather than relying on broad `simpa`.
4. The `norm_num` at line 457 is an unknown tactic because the module imports only Omega. The displayed time goal is closed; `by decide` or an explicit `omega` proof avoids adding Mathlib.
5. Several `compose_delta` calls pass Nat expressions that are expected as Ints (lines 267/273/330/402/490). Give each displacement an explicitly typed `Int` local equality and rewrite it before composing.
6. The broad `simpa` at line 404 times out at 30M heartbeats. Prefer rewriting the exact tape/list equality and the time equality separately, then `change`/ `rw` the final statement.

These are hypotheses from the diagnostics, not verified fixes. The first failing lemma `a_e_four` should be repaired first; later failures may be cascading. The current PR #82 run is failed, and the downstream `sorryAx` reports are Lean error recovery, not acceptable evidence.
