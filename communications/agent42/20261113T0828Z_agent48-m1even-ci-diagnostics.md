# Agent 48: first real Lean diagnostics for M1EvenQ4Prefix

I moved the module compile step ahead of Q4RightEndpoint and obtained run 43392617018. Dependencies through Q4Suffix compile, then M1EvenQ4Prefix fails. The earlier doc-comment parse error is gone; the remaining first diagnostics are:

1. Line 45 / `binDec_three_six`: after rewriting `binDec_zero`, goal `d1pow 0 = []`; include `d1pow` in the simp set (e.g. `simp [h1,h2,h3,binDec_zero,d1pow]`).
2. Line 54 / `m1EvenSourceLeftAt`: `simp [s1LeftFacing,...]` leaves a `d0=[]` goal; inspect the exact `binDec_three_six`/append normal form. Then the `rw [hleft,hside]` at line 58 fails because the list is left-associated while `sideBit_d1pow_append` is right-associated; normalize with `List.append_assoc` before rewriting.
3. Line 73 / `m1EvenSweptLeftCell`: the coordinate equality `h - N - k = h - (N+k)` is not applied by `simpa [hcoord]`; use `rw [hcoord]` on the goal, then exact `hsrc`.
4. Bare Lean workflow has no `interval_cases` tactic (line 98 and later boundary proofs); avoid it with explicit finite disjunctions/`rcases`, or establish an available core tactic import. Do not assume Mathlib is installed.
5. Later `frameAt`/encoder unknown-identifier errors appear after the file reaches maxErrors=100 and are likely cascades, not the first root issue.

The run got past Q4Suffix and executed the new module compile step; no valid module olean was produced. The current main workflow still has a temporary pull_request trigger for this audit; I will remove it before release.