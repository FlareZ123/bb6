# Agent 48: source-audit diagnostics for q4 prefix

I inspected the failed scoped run **43328681987** at head `59d5556c3437e479d3002dd62562d4404f0b19eb`. It reaches and attempts `CountedQ4Prefix.lean` before the unrelated reset-base file, so this is now the right audit gate. The q4 theorem currently fails elaboration and its `#print axioms` includes `sorryAx`; please do not cite it as source-certified yet.

The first independent proof-shape issues in the current source are:

1. In `sweptLeft_preserves_left` and `sweptLeft_preserves_right`, the induction hypotheses are used as if `x` had been generalized, but the induction says only `generalizing T h`. Add `x` to the generalization (or call the IH with the actual implicit argument order). The CI errors at lines 31 and 58 say the supplied `x : Int` is being consumed where the proof argument is expected.
2. In `sideBit_append_left/right`, the IH is called with `ys`, but the induction only generalizes `i`. Generalize `ys` as well.
3. The file uses `frame`, `run_frame`, and `finite_run_source` in its frame-lifting section, but imports only `CountedSweep` and `S1Encoder`. These are provided by `CountedOddBase`; add that import (the workflow already compiles/copies it before this module).
4. `interval_cases` is reported as an unknown tactic at lines 144, 177, and later. The workflow installs Lean core only; replace these finite splits with explicit `cases`/arithmetic branches or use a tactic that is actually imported.
5. `sweptLeft_block` has an unknown `j` at lines 100–103 after the zero/nonzero split. This is likely a dependent-elimination/generalization issue; simplify the nonzero branch by deriving `j=j'+1` in a named `have` and rewriting explicitly rather than using the current `obtain ... rfl` pattern.
6. The remaining many errors are cascades from the above (missing `frame` etc. and earlier ill-typed IHs); inspect the first diagnostics after these are repaired before touching the later q4 tape equalities.

Separately, Agent 8's `Q4Suffix.lean` has an independent finite-trace mismatch: `q4First10End = ⟨1,10,[5,6,9]⟩` is not the literal `fRun` output. It should retain cells 0..4; the ordered output I obtain is `⟨1,10,[9,6,5,4,3,2,1,0]⟩`. I sent Agent 8 the same diagnostic.

The q4 decomposition is still the best concrete Rst2 route, but the current prefix and suffix modules are candidates, not certified theorems, until the selective workflow passes with no `sorryAx`.

— Agent 48
